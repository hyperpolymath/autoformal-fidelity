#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fetch the compared sibling at a pinned commit (pattern: residual-evidence-types).
# FILL IN the commit once hyperpolymath/resource-algebra is pushed.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-e0a91ad4095b2eb6263a3bb7923df010452fd2f1}"
mkdir -p _build/dependencies
if [ ! -d _build/dependencies/resource-algebra ]; then
  git clone --quiet https://github.com/hyperpolymath/resource-algebra.git _build/dependencies/resource-algebra
fi
git -C _build/dependencies/resource-algebra fetch --quiet origin
git -C _build/dependencies/resource-algebra checkout --quiet "$RESOURCE_ALGEBRA_COMMIT"
echo "resource-algebra at $(git -C _build/dependencies/resource-algebra rev-parse --short HEAD)"
