set -euxo pipefail

main() {
    if [ $TARGET != x86_64-unknown-linux-gnu ] || [ $TRAVIS_BRANCH != master ]; then
        return
    fi

    cargo doc

    mkdir ghp-import

    curl -Ls https://github.com/davisp/ghp-import/archive/master.tar.gz | \
        tar --strip-components 1 -C ghp-import -xz

    ./ghp-import/ghp_import.py target/doc

    set +x
    git push -fq https://$GH_TOKEN@github.com/$TRAVIS_REPO_SLUG.git gh-pages && \
        echo OK
}

main
