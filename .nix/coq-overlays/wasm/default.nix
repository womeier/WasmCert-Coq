{
  lib,
  mkCoqDerivation,
  which,
  coq,
  flocq,
  parseque,
  mathcomp,
  compcert,
  ExtLib,
  makeWrapper,
  version ? null,
}:

with lib;
mkCoqDerivation {
  pname = "wasm";
  repo = "WasmCert-Coq";
  owner = "WasmCert";

  inherit version;

  mlPlugin = true;
  useDune = true;

  buildInputs = [
    ExtLib
    mathcomp.ssreflect
    parseque
    flocq
    compcert
    coq.ocamlPackages.mdx
    coq.ocamlPackages.linenoise
    coq.ocamlPackages.wasm
    makeWrapper
  ];
  propagatedBuildInputs = [ ];

  releaseRev = v: "v${v}";

  installPhase = ''
    runHook preInstall
    dune install -p coq-wasm --prefix=$out --libdir $OCAMLFIND_DESTDIR
    wrapProgram $out/bin/wasm_coq_interpreter --prefix OCAMLPATH : $OCAMLPATH
    runHook postInstall
  '';

  meta = {
    description = "Wasm mechanisation in Coq/Rocq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
