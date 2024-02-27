#!/usr/bin/env bash

set -v -e -x

# VS code server
curl -L https://github.com/gitpod-io/openvscode-server/releases/download/openvscode-server-v1.86.2/openvscode-server-v1.86.2-linux-x64.tar.gz --output server.tar.gz
tar -xzf server.tar.gz
rm server.tar.gz

OPENVSCODE=$HOME/openvscode-server-v1.86.2-linux-x64/bin/openvscode-server

${OPENVSCODE} --install-extension /tmp/FStarLang.fstar-vscode-assistant-0.6.1.vsix
${OPENVSCODE} --install-extension rust-lang.rust-analyzer
