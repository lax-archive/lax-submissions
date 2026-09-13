import Lax17Proofs.Source.ChekuriChuzhoyCorollary32Contract
import Lax17Proofs.Source.ChekuriChuzhoyStitchedRows

namespace Lax17Proofs

universe u v w

/-!
# Downstream Chekuri--Chuzhoy contract adapter

The named paper contracts are split across:

* `ChekuriChuzhoyTheorem215Contract`
* `ChekuriChuzhoyTheoremB1Contract`
* `ChekuriChuzhoyTheorem31Contract`
* `ChekuriChuzhoyCorollary32Contract`

This file keeps the narrow specialized interface consumed by the existing
Appendix C.1 formalization in `ChekuriChuzhoy.lean`: Corollary 3.2 at the exact
parameters used in Corollary 3.3, returning either a direct grid minor or the
stitched-row object already handled by the full proof file.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract



end ChekuriChuzhoyContract
end SimpleGraph

end Lax17Proofs
