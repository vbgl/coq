#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8457" ] || [ "$CI_BRANCH" = "simplex" ]; then
        fiat_crypto_CI_REF=simplex
        fiat_crypto_CI_GITURL=https://github.com/vbgl/fiat-crypto
fi
