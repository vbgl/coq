if [ "$CI_PULL_REQUEST" = "11018" ] || [ "$CI_BRANCH" = "lia-in-auto-with-zarith" ]; then

    bignums_CI_REF=auto-with-zarith
    bignums_CI_GITURL=https://github.com/vbgl/bignums

    compcert_CI_REF=auto-with-zarith
    compcert_CI_GITURL=https://github.com/vbgl/CompCert

fi
