#!/bin/bash

# Check if all arguments are provided
if [ -z "$1" ] || [ -z "$2" ]; then
    echo "Error: All arguments are required"
    echo "Usage: ./prepare-deploy.sh bn254 <huff|yul>"
    echo "Example: ./prepare-deploy.sh bn254 huff"
    exit 1
fi

CURVE=$1
TYPE=$2

# Validate curve argument
if [ "$CURVE" != "bn254" ]; then
    echo "Error: Curve must be 'bn254'"
    exit 1
fi

# Validate type argument
if [ "$TYPE" != "huff" ] && [ "$TYPE" != "yul" ]; then
    echo "Error: Type must be 'huff' or 'yul'"
    exit 1
fi

BASE_DIR="deployed-artifacts/$CURVE-$TYPE"

# Find the latest version and return next version
get_next_version() {
    if [ ! -d "$BASE_DIR" ]; then
        echo "v1"
        return
    fi

    latest=$(ls -1 "$BASE_DIR" 2>/dev/null | grep -E '^v[0-9]+$' | sed 's/v//' | sort -n | tail -1)
    if [ -z "$latest" ]; then
        echo "v1"
    else
        echo "v$((latest + 1))"
    fi
}

NEW_VERSION=$(get_next_version)
DEPLOY_DIR="$BASE_DIR/$NEW_VERSION"

echo "Creating version: $NEW_VERSION"

mkdir -p "$DEPLOY_DIR"

if [ "$TYPE" = "huff" ]; then
    huffc ./src/$CURVE/huff/Poseidon2.huff -b > "$DEPLOY_DIR/Poseidon2huff.out"
    echo "Deployment files prepared in $DEPLOY_DIR"
elif [ "$TYPE" = "yul" ]; then
    # Capitalize first letter of curve for the JSON filename
    CURVE_UPPER="$(echo "${CURVE:0:1}" | tr '[:lower:]' '[:upper:]')${CURVE:1}"
    cp "out/Poseidon2Yul.sol/Poseidon2Yul_${CURVE_UPPER}.json" "$DEPLOY_DIR/Poseidon2Yul_${CURVE_UPPER}.json"
    echo "Deployment files prepared in $DEPLOY_DIR"
fi
