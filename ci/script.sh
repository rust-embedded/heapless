set -euxo pipefail

main() {
    cargo check --target $TARGET
    cargo check --target $TARGET --features 'serde'

    if [ $TARGET = x86_64-unknown-linux-gnu ]; then
        cargo test --target $TARGET --features 'serde'
        cargo test --target $TARGET --release --features 'serde'

        if [ $TRAVIS_RUST_VERSION = nightly ]; then
            export RUSTFLAGS="-Z sanitizer=thread"
            export RUST_TEST_THREADS=1
            export TSAN_OPTIONS="suppressions=$(pwd)/suppressions.txt"

            cargo test --test tsan --target $TARGET
            cargo test --test tsan --target $TARGET --release
        fi
    fi
}

# fake Travis variables to be able to run this on a local machine
if [ -z ${TRAVIS_BRANCH-} ]; then
    TRAVIS_BRANCH=auto
fi

if [ -z ${TRAVIS_PULL_REQUEST-} ]; then
    TRAVIS_PULL_REQUEST=false
fi

if [ -z ${TRAVIS_RUST_VERSION-} ]; then
    case $(rustc -V) in
        *nightly*)
            TRAVIS_RUST_VERSION=nightly
            ;;
        *beta*)
            TRAVIS_RUST_VERSION=beta
            ;;
        *)
            TRAVIS_RUST_VERSION=stable
            ;;
    esac
fi

if [ -z ${TARGET-} ]; then
    TARGET=$(rustc -Vv | grep host | cut -d ' ' -f2)
fi

if [ $TRAVIS_BRANCH != master ]; then
    main
fi
