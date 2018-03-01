set -euxo pipefail

main() {
    # install latest Xargo
    local tag=$(git ls-remote --tags --refs --exit-code https://github.com/japaric/xargo \
                    | cut -d/ -f3 \
                    | grep -E '^v[0-9.]+$' \
                    | sort --version-sort \
                    | tail -n1)
    curl -LSfs https://japaric.github.io/trust/install.sh | \
        sh -s -- \
           --force \
           --git japaric/xargo \
           --target x86_64-unknown-linux-musl \
           --tag $tag

    rustup component list | grep 'rust-src.*installed' || \
        rustup component add rust-src
}

main
