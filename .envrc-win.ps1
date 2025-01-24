$env:VSCODE_INJECTION = 1  # seems not passed automatically to custom profiles
& (code --locate-shell-integration-path pwsh)
.\.env\Scripts\activate
