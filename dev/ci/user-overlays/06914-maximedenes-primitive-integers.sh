if [ "$CI_PULL_REQUEST" = "6914" ] || [ "$CI_BRANCH" = "primitive-integers" ]; then

    bignums_CI_BRANCH=primitive-integers
    bignums_CI_GITURL=https://github.com/vbgl/bignums

    CompCert_CI_BRANCH=primitive-integers
    CompCert_CI_GITURL=https://github.com/vbgl/CompCert

fi
