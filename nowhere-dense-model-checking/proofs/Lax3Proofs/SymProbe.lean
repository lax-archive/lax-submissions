import Lax3Proofs.SolveAugBaseFrame
set_option autoImplicit false
namespace Probe
example (m : ℕ) (f : ℕ → ℕ) (h : ((List.range m).map f).Nodup) (a b : ℕ)
    (ha : a < m) (hb : b < m) (hf : f a = f b) : a = b :=
  List.inj_on_of_nodup_map h (List.mem_range.2 ha) (List.mem_range.2 hb) hf
example (m : ℕ) (f : ℕ → ℕ) (hinj : ∀ a b, a < m → b < m → f a = f b → a = b) :
    ((List.range m).map f).Nodup :=
  List.Nodup.map_on (fun a ha b hb hab =>
    hinj a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab) (List.nodup_range)
end Probe
