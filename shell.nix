with import <nixpkgs> {};

stdenv.mkDerivation {
    name = "lean-slides";
    buildInputs = [
        pandoc_3_5
        nodejs
	nodePackages.browser-sync
    ];
    # shellHook = ''
    #     export PATH="$PWD/node_modules/.bin/:$PATH"
    # '';
}
