#!/bin/bash
# Install bender and verilator for the axi project.
#
# bender: hardware dependency manager (pulp-platform/bender)
# verilator: SystemVerilog linter/simulator

set -euo pipefail

BENDER_VERSION="${BENDER_VERSION:-0.31.0}"
INSTALL_DIR="${INSTALL_DIR:-/usr/local/bin}"

require_cmd() {
    if ! command -v "$1" &>/dev/null; then
        echo "error: required command '$1' not found" >&2
        exit 1
    fi
}

install_verilator() {
    if command -v verilator &>/dev/null; then
        echo "verilator already installed: $(verilator --version | head -1)"
        return
    fi

    require_cmd apt-get
    echo "Installing verilator..."
    apt-get install -y verilator
}

bender_arch() {
    case "$(uname -m)" in
        x86_64|amd64) echo "x86_64" ;;
        aarch64|arm64) echo "arm64" ;;
        *)
            echo "error: unsupported architecture for bender: $(uname -m)" >&2
            exit 1
            ;;
    esac
}

bender_os_id() {
    . /etc/os-release
    case "${ID}" in
        ubuntu|debian) echo "${ID}${VERSION_ID}" ;;
        *)
            echo "error: unsupported OS for bender binary: ${ID}-${VERSION_ID}" >&2
            exit 1
            ;;
    esac
}

install_bender() {
    if command -v bender &>/dev/null; then
        echo "bender already installed: $(bender --version)"
        return
    fi

    require_cmd curl
    require_cmd tar
    require_cmd install

    echo "Installing bender v${BENDER_VERSION}..."
    ARCH="$(bender_arch)"
    OS_ID="$(bender_os_id)"
    TARBALL="bender-${BENDER_VERSION}-${ARCH}-linux-gnu-${OS_ID}.tar.gz"
    URL="https://github.com/pulp-platform/bender/releases/download/v${BENDER_VERSION}/${TARBALL}"
    TMP="$(mktemp -d)"
    trap 'rm -rf "${TMP}"' RETURN

    curl --fail --location --show-error --silent "${URL}" -o "${TMP}/bender.tar.gz"
    tar -xzf "${TMP}/bender.tar.gz" -C "${TMP}"
    install -m 755 "${TMP}/bender" "${INSTALL_DIR}/bender"
}

install_verilator
install_bender

echo ""
echo "Installed:"
verilator --version | head -1
bender --version
