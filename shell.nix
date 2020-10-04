{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs;
  in
pkgs.mkShell {
  buildInputs = (with pkgs.idrisPackages; [
    (with-packages [base contrib prelude])
    ]);

}
