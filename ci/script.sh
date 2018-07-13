set -euxo pipefail

main() {
    cargo check --target $TARGET

    if [ $TARGET = x86_64-unknown-linux-gnu ]; then
        cargo test --target $TARGET
        cargo test --target $TARGET --no-default-features
        cargo test --target $TARGET --release
        cargo test --target $TARGET --release --no-default-features

        export RUSTFLAGS="-Z sanitizer=thread"
        export RUST_TEST_THREADS=1
        export TSAN_OPTIONS="suppressions=$(pwd)/blacklist.txt"

        cargo test --test tsan --target $TARGET
        cargo test --test tsan --target $TARGET --no-default-features
        cargo test --test tsan --target $TARGET --release
        cargo test --test tsan --target $TARGET --release --no-default-features
    fi
}

if [ $TRAVIS_BRANCH != master ]; then
    main
fi
