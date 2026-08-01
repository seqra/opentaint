BeforeAll {
    $installer = Get-Content (Join-Path $PSScriptRoot "install.ps1") -Raw
    $installer = $installer -replace '(?m)^Main\s*$', ''
    Invoke-Expression $installer
}

Describe "Resolve-FloatingSelector pagination" {
    BeforeEach {
        Mock Invoke-RestMethod {
            param($Uri, $Headers, [switch]$UseBasicParsing)

            if ($Uri -match 'page=1$') {
                return 1..100 | ForEach-Object {
                    [pscustomobject]@{ tag_name = "analyzer/2026.01.$_.abcdef0" }
                }
            }
            if ($Uri -match 'page=2$') {
                return @(
                    [pscustomobject]@{ tag_name = "v0.4.5" },
                    [pscustomobject]@{ tag_name = "v0.5.1" }
                )
            }
            throw "unexpected page: $Uri"
        }
    }

    It "resolves a major selector from a later page" {
        Resolve-FloatingSelector -Selector "v0" | Should -Be "v0.5.1"
        Should -Invoke Invoke-RestMethod -Times 2
    }

    It "resolves a minor selector from a later page" {
        Resolve-FloatingSelector -Selector "v0.4" | Should -Be "v0.4.5"
        Should -Invoke Invoke-RestMethod -Times 2
    }
}

Describe "Test-Version prerelease support" {
    It "keeps exact prerelease installation supported" {
        $result = Test-Version -Raw "v0.4.5-rc.1"
        $result.Tag | Should -Be "v0.4.5-rc.1"
        $result.PathSegment | Should -Be "download/v0.4.5-rc.1"
    }
}
