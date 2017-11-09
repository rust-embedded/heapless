set -euxo pipefail

main() {
    case $TARGET in
        thumb*m-none-eabi)
            local vers=0.3.8

            cargo install --list | grep "xargo v$vers" || \
                ( cd .. && cargo install xargo -f --vers $vers )

            rustup component list | grep 'rust-src.*installed' || \
                rustup component add rust-src
            ;;
        x86_64-unknown-linux-gnu)
            ;;
        *)
            # unhandled case
            exit 1
            ;;
    esac
}

main
