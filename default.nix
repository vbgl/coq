# How to use?

# If you have Nix installed, you can compile Coq and “install” it by running:
# $ make clean # (only needed if you have left-over compilation files)
# $ nix-build
# at the root of the Coq repository.
# nix-build also supports the --arg option, so you will be able to do:
# $ nix-build --arg buildIde false
# if you do not want to build the CoqIDE
# Once the build is finished, you will find, in the current directory,
# a symlink to where Coq was installed.

{ pkgs ? import ./dev/nixpkgs.nix {}
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_09
, buildIde ? true
, buildDoc ? false # This is broken: “package coq does not exist”
, coq-version ? "8.14-git"
}:

let

inherit (pkgs) stdenv dune_2 glib gnome3 wrapGAppsHook pkg-config python3 antlr4;

coq = stdenv.mkDerivation {
  pname = "coq";
  version = coq-version ;

  src = with builtins; filterSource
  (path: _:
    !elem (baseNameOf path) [ ".git" "result" "bin" "_build" "_build_ci" "nix" "default.nix" ]) ./.;

  dontConfigure = true;

  buildInputs = [ dune_2 ]
  ++ (with ocamlPackages; [ ocaml findlib num zarith ])
  ;

  # Since #12604, ocamlfind looks for num when building plugins
  # This follows a similar change in the nixpkgs repo (cf. NixOS/nixpkgs#94230)
  # Same for zarith which is needed since its introduction as a dependency of Coq
  propagatedBuildInputs = with ocamlPackages; [ zarith ];

  buildPhase = ''
    runHook preBuild
    patchShebangs dev/tools
    dune build -p $pname
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dune install --sections=lib,stublibs --libdir=$OCAMLFIND_DESTDIR $pname
    dune install --sections=lib_root,bin,doc,man --prefix=$out $pname
    ln -s $OCAMLFIND_DESTDIR/coq/plugins $out/lib/coq/
    runHook postInstall
  '';

};

coqide-server = stdenv.mkDerivation {
  pname = "coqide-server";
  inherit (coq) version src dontConfigure;

  propagatedBuildInputs = [ coq ];
  buildInputs = [ dune_2 ]
  ++ (with ocamlPackages; [ ocaml findlib num zarith ])
  ;

  buildPhase = ''
    runHook preBuild
    dune build -p $pname
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix=$out --libdir=$OCAMLFIND_DESTDIR $pname
    runHook postInstall
  '';

};

coqide = stdenv.mkDerivation {
  pname = "coqide";
  inherit (coq) version src dontConfigure;

  propagatedBuildInputs = [ coqide-server ];
  buildInputs = [ dune_2 glib gnome3.defaultIconTheme wrapGAppsHook ]
  ++ (with ocamlPackages; [ ocaml findlib lablgtk3-sourceview3 ])
  ;

  buildPhase = ''
    runHook preBuild
    dune build -p $pname
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix=$out $pname
    runHook postInstall
  '';

};

coq-doc = stdenv.mkDerivation {
  pname = "coq-doc";
  inherit (coq) version src dontConfigure;

  buildInputs = [ dune_2 coq
    pkg-config (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
    antlr4 ]
  ++ (with ocamlPackages; [ ocaml findlib odoc ])
  ;

  buildPhase = ''
    runHook preBuild
    #substituteInPlace doc/dune --replace 'COQLIB=%{project_root}' 'COQLIB=${coq}/lib/coq/'
    patchShebangs doc/stdlib/make-library-index
    echo DEBUG 0
    ocamlfind list
    echo DEBUG 1
    ocamlfind query -r coq
    echo DEBUG 2
    dune build -p $pname
    runHook postBuild
  '';

};

in

{ inherit coq; }
// (if buildIde then { inherit coqide; } else {})
// (if buildDoc then { inherit coq-doc; } else {})
