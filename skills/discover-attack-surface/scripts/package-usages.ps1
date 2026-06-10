<#
package-usages.ps1 <model-dir> <package>

Windows equivalent of package-usages.sh: print the distinct methods of dependency
<package> that the project's OWN compiled classes call. Scans every moduleClasses
entry in <model-dir>/project.yaml (class dirs or jars) and keeps only call sites
whose owner is in <package>, deduped. When the modules carry a `packages:` list,
only classes under those roots are scanned; otherwise moduleClasses is already
project-only. The separate `dependencies:` list is never touched.
#>
param(
  [Parameter(Mandatory)][string]$ModelDir,
  [Parameter(Mandatory)][string]$Package
)

$pp   = $Package -replace '\.','/'
$yaml = Get-Content (Join-Path $ModelDir 'project.yaml')

# read a YAML block list — the "- item" lines under <key>:
function Get-YamlList([string]$key) {
  $f = $false
  foreach ($l in $yaml) {
    if ($l -match "^\s*$key:\s*$") { $f = $true; continue }
    if ($f) {
      if ($l -match '^\s*-\s+(.+?)\s*$' -and $l -notmatch ':') { $Matches[1] }
      elseif ($l -match ':') { $f = $false }
    }
  }
}

$roots = (Get-YamlList 'packages' | ForEach-Object { [regex]::Escape(($_ -replace '\.','/')) }) -join '|'

$out = foreach ($e in (Get-YamlList 'moduleClasses')) {
  $p = Join-Path $ModelDir $e
  if (Test-Path -LiteralPath $p -PathType Container) {
    $base  = (Resolve-Path -LiteralPath $p).Path
    $names = Get-ChildItem -LiteralPath $p -Recurse -Filter *.class |
      ForEach-Object { ($_.FullName.Substring($base.Length).TrimStart('\','/') -replace '\.class$','') -replace '[\\/]','.' }
  } else {
    $names = & jar tf $p | Where-Object { $_ -match '\.class$' } |
      ForEach-Object { ($_ -replace '\.class$','') -replace '/','.' }
  }
  if ($roots) { $names = $names | Where-Object { ($_ -replace '\.','/') -match "^($roots)/" } }
  if ($names) {
    $argfile = New-TemporaryFile          # pass class names via @argfile to dodge command-line length limits
    $names | Set-Content -LiteralPath $argfile
    & javap -c -p -classpath $p "@$argfile" 2>$null
    Remove-Item -LiteralPath $argfile
  }
}

$out |
  Select-String -Pattern ("// (Interface)?Method " + [regex]::Escape($pp) + "/\S+") -AllMatches |
  ForEach-Object { $_.Matches } | ForEach-Object { $_.Value } |
  Sort-Object -Unique
