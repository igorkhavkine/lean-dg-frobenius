$env:VSCODE_INJECTION = 1  # seems not passed automatically to custom profiles
. (code --locate-shell-integration-path pwsh)
if (Test-Path ".\.env\Scripts\activate.ps1") {
    . .\.env\Scripts\activate.ps1
}
