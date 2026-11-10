module

public import ArtinMatthews.SLocalHilbertForm
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual alternation of the Hilbert product when -1 is an n-th power.
This includes exponents 2,3,6 in a field containing a primitive twelfth
root. The characteristic-two case is not deduced from skew-symmetry. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open GlobalClassFieldTheory.Reciprocity
open scoped NumberField BigOperators Classical
noncomputable section

theorem localHilbertPairing_diag_eq_one (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hminus : (-1 : Fˣ) ∈ (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range)
    (q : PowerClassGroup F n) : localHilbertPairing F n hnF hmu q q = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : Fˣ, powerClass F n a = q :=
    QuotientGroup.mk'_surjective _ q
  rw [localHilbertPairing_powerClass]
  let e := nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
  change e (LocalClassFieldTheory.Kummer.localHilbertSymbol F n hnF hmu a a) = 1
  have hneg := LocalClassFieldTheory.Kummer.localHilbertSymbol_neg_self F n hnF hmu a
  have hm := LocalClassFieldTheory.Kummer.localHilbertSymbol_mul_right F n hnF hmu a (-1) a
  have hmul : (-1 : Fˣ) * a = -a := by ext; simp
  rw [hmul,
    (LocalClassFieldTheory.Kummer.localHilbertSymbol_right_kernel F n hnF hmu (-1)).mpr hminus a,
    one_mul] at hm
  rw [← hm, hneg, map_one]

variable (K : Type) [Field K] [NumberField K]

theorem finitePlaceAdicHilbertPairing_diag_eq_one
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hminus : ∃ a : Kˣ, a ^ (n : ℕ) = -1)
    (v : HeightOneSpectrum (𝓞 K)) (q : PowerClassGroup (v.adicCompletion K) n) :
    finitePlaceAdicHilbertPairingFamily K n hmu v q q = 1 := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hnC : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty :=
    finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  have hnegC : (-1 : Cˣ) ∈ (powMonoidHom (n : ℕ) : Cˣ →* Cˣ).range := by
    obtain ⟨a, ha⟩ := hminus
    refine ⟨Units.map (algebraMap K C).toMonoidHom a, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, ha]
    apply Units.ext
    simp
  change hilbertPairingOfRingEquiv (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
    (localHilbertPairing C n hnC hmuC) q q = 1
  rw [hilbertPairingOfRingEquiv_apply, localHilbertPairing_diag_eq_one C n hnC hmuC hnegC,
    map_one]

theorem sLocalHilbertForm_diag_eq_one
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hminus : ∃ a : Kˣ, a ^ (n : ℕ) = -1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S) :
    sLocalHilbertForm K n hmu S x x = 1 := by
  rw [sLocalHilbertForm_apply]
  apply Finset.prod_eq_one
  intro v _
  rw [finitePlaceAdicHilbertPairing_diag_eq_one K n hmu hminus, map_one]

omit [NumberField K] in
theorem neg_one_is_sixth_power_of_primitive_twelve {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) : ∃ a : Kˣ, a ^ 6 = -1 := by
  refine ⟨(hζ.isUnit (by decide)).unit, ?_⟩
  apply Units.ext
  change ζ ^ 6 = -1
  exact (hζ.pow_of_dvd (p := 6) (by decide) (by decide)).eq_neg_one_of_two_right

omit [NumberField K] in
theorem neg_one_is_square_of_primitive_twelve {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) : ∃ a : Kˣ, a ^ 2 = -1 := by
  obtain ⟨a, ha⟩ := neg_one_is_sixth_power_of_primitive_twelve K hζ
  exact ⟨a ^ 3, by rw [← pow_mul]; exact ha⟩

omit [NumberField K] in
theorem neg_one_is_cube_of_primitive_twelve {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) : ∃ a : Kˣ, a ^ 3 = -1 := by
  obtain ⟨a, ha⟩ := neg_one_is_sixth_power_of_primitive_twelve K hζ
  exact ⟨a ^ 2, by rw [← pow_mul]; exact ha⟩

end
end ArtinMatthews
