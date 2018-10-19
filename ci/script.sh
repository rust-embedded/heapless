set -euxo pipefail

main() {
    cargo check --target $TARGET
    if [ $TRAVIS_RUST_VERSION = nightly ]; then
        cargo check --target $TARGET --features 'const-fn smaller-atomics'
    fi

    if [ $TARGET = x86_64-unknown-linux-gnu ]; then
        cargo test --target $TARGET
        cargo test --target $TARGET --release

        if [ $TRAVIS_RUST_VERSION = nightly ]; then
            cargo test --target $TARGET --features 'const-fn smaller-atomics'
            cargo test --target $TARGET --release --features 'const-fn smaller-atomics'

            export RUSTFLAGS="-Z sanitizer=thread"
            export RUST_TEST_THREADS=1
            export TSAN_OPTIONS="suppressions=$(pwd)/blacklist.txt"

            cargo test --test tsan --target $TARGET
            cargo test --test tsan --target $TARGET --features 'const-fn smaller-atomics'
            cargo test --test tsan --target $TARGET --release
            cargo test --test tsan --target $TARGET --release --features 'const-fn smaller-atomics'
        fi
    fi
}

if [ $TRAVIS_BRANCH != master ]; then
    main
fi
