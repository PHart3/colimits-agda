## Summary

This directory contains a formalized direct proof of the fact that
all ordinary colimits enjoy pullback stability (`Stability-ord.agda`).
This fact in a slightly different form is stated for all ordinary
colimits over reflexive graphs by Corollary 3.5.10 of Rijke's thesis,
*Classying Types*. We also construct the cogap map for pullback stability
in the coslice category of types (`Stability-cos-coc.agda`).

On paper, we have used these facts to show that coslice colimits over trees
enjoy pullback stability (see Theorem 16 of the CSL paper).

## Manual Type-Checking

1. Install Agda 2.6.3 or 2.6.4.
2. Add `stab.agda-lib` and `../HoTT-Agda/hott-core.agda-lib` to your Agda libraries file.
3. Type check the files `Stability-ord.agda` and `Stability-cos-coc.agda`.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
