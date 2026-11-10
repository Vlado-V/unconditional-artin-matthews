module

public import ArtinMatthews.ArtinAbelianEulerLog
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Global Dedekind/Artin factorization in the domain of absolute convergence.
Every finite prime, including every ramified prime, is represented by its
actual inertia-fixed local factor. -/
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

local instance globalEulerCharacterFintype : Fintype (Gal(E/F) →* ℂˣ) := Fintype.ofFinite _

/-- The actual Dedekind zeta function factors into the genuine abelian Artin
Euler products, with no excluded primes and no assumed factorization law. -/
theorem dedekindZeta_eq_prod_abelianArtinEulerProduct {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s =
      ∏ χ : Gal(E/F) →* ℂˣ, abelianArtinEulerProduct F E χ s := by
  have h := hasProd_prod (s := (Finset.univ : Finset (Gal(E/F) →* ℂˣ)))
    (fun χ _ => abelianArtinEulerProduct_hasProd F E χ hs)
  have hζ := dedekindZeta_hasProd_exp_localLog E hs
  apply hζ.unique
  exact h.congr_fun (fun p =>
    (dedekindEulerLocalLog_exp E p hs).trans
      (prod_abelianArtinRationalFactor F E p s).symm)

/-- The trivial global character recovers the actual base-field zeta function. -/
theorem abelianArtinEulerProduct_one {s : ℂ} (hs : 1 < s.re) :
    abelianArtinEulerProduct F E 1 s = NumberField.dedekindZeta F s := by
  apply (abelianArtinEulerProduct_hasProd F E 1 hs).unique
  apply (dedekindZeta_hasProd_exp_localLog F hs).congr_fun
  intro p
  rw [dedekindEulerLocalLog_exp F p hs]
  unfold abelianArtinRationalFactor
  apply Finset.prod_congr rfl
  intro P _
  simp [abelianArtinLocalFactor, primeOverHeightOne]

end ArtinMatthews.AbelianLocal
