param(
  [Parameter(Mandatory)][string]$ModelDir,
  [Parameter(Mandatory)][string]$Module
)

$yaml = Get-Content (Join-Path $ModelDir 'project.yaml') -ErrorAction SilentlyContinue
$dirs = @()
$in = $false
foreach ($l in $yaml) {
  if ($l -match '^goProjects:') { $in = $true; continue }
  if ($in -and $l -match '^[^\s-]') { $in = $false }
  if ($in -and $l -match 'projectDir:\s*(.+?)\s*$') { $dirs += $Matches[1] }
}
if (-not $dirs) { $dirs = @($ModelDir) }

$out = foreach ($d in $dirs) {
  if (-not (Test-Path -LiteralPath $d -PathType Container)) { $d = Join-Path $ModelDir $d }
  $files = Get-ChildItem -LiteralPath $d -Recurse -Filter *.go -ErrorAction SilentlyContinue |
    Where-Object { Select-String -LiteralPath $_.FullName -Pattern ('"' + $Module) -SimpleMatch -Quiet }
  foreach ($f in $files) {
    $imports = @{}
    $blk = $false
    foreach ($l in (Get-Content -LiteralPath $f.FullName)) {
      if ($l -match '^import\s*\(') { $blk = $true; continue }
      if ($blk -and $l -match '^\)') { $blk = $false; continue }
      if (($blk -or $l -match '^import\s') -and $l -match '"([^"]+)"') {
        $path = $Matches[1]
        if ($path -eq $Module -or $path.StartsWith("$Module/")) {
          $imports[$path] = ($l -replace '"[^"]*".*$', '' -replace '^\s*import', '').Trim()
        }
      }
    }
    foreach ($path in $imports.Keys) {
      $id = $imports[$path]
      if (-not $id) {
        Push-Location $d
        $id = & go list -f '{{.Name}}' $path 2>$null
        Pop-Location
      }
      if (-not $id) { $id = ($path -split '/')[-1] }
      $pattern = '\b' + [regex]::Escape($id) + '\.([A-Z][A-Za-z0-9_]*)'
      Select-String -LiteralPath $f.FullName -Pattern $pattern -AllMatches |
        ForEach-Object { $_.Matches } | ForEach-Object { "$path." + $_.Groups[1].Value }
    }
  }
}

$out | Sort-Object -Unique
