# How to use?

# If you have Nix installed, you can get in an environment with everything
# needed to compile Coq and CoqIDE by running:
# $ nix-shell
# at the root of the Coq repository.

# How to tweak default arguments?

# nix-shell supports the --arg option (see Nix doc) that allows you for
# instance to do this:
# $ nix-shell --arg ocamlPackages "(import <nixpkgs> {}).ocaml-ng.ocamlPackages_4_05" --arg buildIde false

# You can also compile Coq and "install" it by running:
# $ make clean # (only needed if you have left-over compilation files)
# $ nix-build
# at the root of the Coq repository.
# nix-build also supports the --arg option, so you will be able to do:
# $ nix-build --arg doInstallCheck false
# if you want to speed up things by not running the test-suite.
# Once the build is finished, you will find, in the current directory,
# a symlink to where Coq was installed.

{ pkgs ? import ./dev/nixpkgs.nix {}
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_09
, buildIde ? true
, buildDoc ? true
, doInstallCheck ? true
, coq-version ? "8.13-git"
}:

with pkgs;
with stdenv.lib;

stdenv.mkDerivation rec {

  name = "coq";

  buildInputs = [
    hostname
    dune_2
    python3 time # coq-makefile timing tools
  ]
  ++ (with ocamlPackages; [ ocaml findlib num zarith ])
  ++ optionals buildIde [
    ocamlPackages.lablgtk3-sourceview3
    glib gnome3.defaultIconTheme wrapGAppsHook
  ]
  ++ optionals buildDoc [
    # Sphinx doc dependencies
    pkg-config (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
    antlr4
    ocamlPackages.odoc
  ]
  ++ optionals doInstallCheck (
    # Test-suite dependencies
    # ncurses is required to build an OCaml REPL
    optional (!versionAtLeast ocaml.version "4.07") ncurses
    ++ [ ocamlPackages.ounit rsync which ]
  )
  ++ optionals true (
    [ jq curl gitFull gnupg ] # Dependencies of the merging script
    ++ (with ocamlPackages; [ merlin ocp-indent ocp-index utop ocamlformat ]) # Dev tools
    ++ [ graphviz ] # Useful for STM debugging
  );

  src = null;

}
