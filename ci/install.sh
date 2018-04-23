set -euxo pipefail

main() {
    if [ $TARGET != x86_64-unknown-linux-gnu ]; then
        rustup target add $TARGET
    fi
}

if [ $TRAVIS_BRANCH != master ]; then
    main
fi
