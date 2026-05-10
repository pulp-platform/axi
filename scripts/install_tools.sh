#!/bin/bash
# Install bender and verilator for the axi project.
#
# bender: hardware dependency manager (pulp-platform/bender)
# verilator: SystemVerilog linter/simulator

set -e

BENDER_VERSION="0.31.0"
INSTALL_DIR="${INSTALL_DIR:-/usr/local/bin}"

# Install verilator via apt
if ! command -v verilator &>/dev/null; then
    echo "Installing verilator..."
    apt-get install -y verilator
else
    echo "verilator already installed: $(verilator --version | head -1)"
fi

# Install bender
if ! command -v bender &>/dev/null; then
    echo "Installing bender v${BENDER_VERSION}..."
    OS_ID=$(. /etc/os-release && echo "${ID}-${VERSION_ID}")
    ARCH=$(uname -m)
    TARBALL="bender-${BENDER_VERSION}-${ARCH}-linux-gnu-${OS_ID}.tar.gz"
    URL="https://github.com/pulp-platform/bender/releases/download/v${BENDER_VERSION}/${TARBALL}"
    TMP=$(mktemp -d)
    curl -sSL "${URL}" -o "${TMP}/bender.tar.gz"
    tar -xzf "${TMP}/bender.tar.gz" -C "${TMP}"
    install -m 755 "${TMP}/bender" "${INSTALL_DIR}/bender"
    rm -rf "${TMP}"
else
    echo "bender already installed: $(bender --version)"
fi

echo ""
echo "Installed:"
verilator --version | head -1
bender --version
