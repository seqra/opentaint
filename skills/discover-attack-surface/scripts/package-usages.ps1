param(
  [Parameter(Mandatory)][string]$ModelDir,
  [Parameter(Mandatory)][string]$Package
)

$pp   = $Package -replace '\.','/'
$yaml = Get-Content (Join-Path $ModelDir 'project.yaml')

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
    $argfile = New-TemporaryFile
    $names | Set-Content -LiteralPath $argfile
    & javap -c -p -classpath $p "@$argfile" 2>$null
    Remove-Item -LiteralPath $argfile
  }
}

$out |
  Select-String -Pattern ("// (Interface)?Method " + [regex]::Escape($pp) + "/\S+") -AllMatches |
  ForEach-Object { $_.Matches } | ForEach-Object { $_.Value } |
  Sort-Object -Unique
