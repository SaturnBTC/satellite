#!/bin/bash

# Script to update the workspace version in Cargo.toml

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

if [ -z "$1" ]; then
    echo "Usage: $0 <new-version>"
    echo "Example: $0 0.31.5"
    exit 1
fi

NEW_VERSION=$1

# Validate version format (basic check)
if ! [[ "$NEW_VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+ ]]; then
    echo "Error: Invalid version format. Expected format: X.Y.Z (e.g., 0.31.5)"
    exit 1
fi

# Check if we're in the workspace root
if [ ! -f "Cargo.toml" ] || ! grep -q "\[workspace.package\]" Cargo.toml; then
    echo "Error: Must be run from the workspace root directory"
    exit 1
fi

# Get current version
CURRENT_VERSION=$(grep -A 2 '\[workspace.package\]' Cargo.toml | grep '^version = ' | sed 's/.*version = "\(.*\)"/\1/')

echo -e "${BLUE}Current workspace version: ${CURRENT_VERSION}${NC}"
echo -e "${BLUE}New workspace version: ${NEW_VERSION}${NC}"
echo ""

# Update version in root Cargo.toml (within [workspace.package] section)
# Match the version line that comes after [workspace.package]
awk -v new_version="${NEW_VERSION}" '
    /\[workspace.package\]/ { in_section=1; print; next }
    in_section && /^version = / { print "version = \"" new_version "\""; in_section=0; next }
    { print }
' Cargo.toml > Cargo.toml.tmp && mv Cargo.toml.tmp Cargo.toml

# Update versions in [workspace.dependencies] section
# Replace version = "X.Y.Z" with the new version in workspace.dependencies
awk -v new_version="${NEW_VERSION}" '
    /\[workspace.dependencies\]/ { in_section=1; print; next }
    in_section && /version = / { 
        # Replace version = "..." with new version, preserving the rest of the line
        gsub(/version = "[^"]*"/, "version = \"" new_version "\"")
        print
        next
    }
    in_section && /^\[/ { in_section=0 }  # Exit section on next [section]
    { print }
' Cargo.toml > Cargo.toml.tmp && mv Cargo.toml.tmp Cargo.toml

echo -e "${GREEN}✓${NC} Updated workspace version to ${NEW_VERSION}"
echo ""
echo "All workspace crates will now use version ${NEW_VERSION}"
echo ""
echo "Next steps:"
echo "  1. Review the changes: git diff Cargo.toml"
echo "  2. Test the build: cargo check --workspace"
echo "  3. Commit the changes"
echo "  4. Publish: ./publish.sh"

