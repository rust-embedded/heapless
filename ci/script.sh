set -euxo pipefail

main() {
    case $TARGET in
        thumb*m-none-eabi)
            xargo check --target $TARGET
            ;;
        *)
            cargo check --target $TARGET
            ;;
    esac
}
