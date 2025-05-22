## Summary

This directory contains a formalized direct proof of the fact that
all ordinary colimits enjoy pullback stability. This fact in a slightly
different form is stated for all ordinary colimits over reflexive graphs
by Corollary 3.5.10 of Rijke's thesis, *Classying Types*. For us, it
means that all coslice colimits over trees enjoy pullback stability
(Theorem 16 of the CSL paper). The proof is in `Stability.agda`.

## Manual Type-Checking

1. Install Agda 2.6.3 or 2.6.4.
2. Add `stab.agda-lib` and `../HoTT-Agda/hott-core.agda-lib` to your Agda libraries file.
3. Type check the file `Stability.agda`.

## License

This work is released under Mozilla Public License 2.0.
See [LICENSE.txt](LICENSE.txt).
