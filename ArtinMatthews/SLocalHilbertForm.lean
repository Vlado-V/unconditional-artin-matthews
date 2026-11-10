module

public import ArtinMatthews.SLocalUnitImage
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicLocalField
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibHilbertProductFormula
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
public import ArtinMatthews.SLocalUnitIsotropy
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertComparison
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
public import Mathlib.Tactic.Basify
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

/-! The genuine product of local Hilbert pairings on the actual finite
S-local power-class space. Nondegeneracy is proved coordinatewise, and
S-unit isotropy is derived from the global reciprocity formula. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sLocalUnitClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →* SLocalPowerClasses K n S where
  toFun a v := powerClass (v.1.adicCompletion K) n
    (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom (a : Kˣ))
  map_one' := by funext v; simp
  map_mul' a b := by funext v; simp

def sLocalRootEquiv (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) :
    rootsOfUnity (n : ℕ) K ≃* rootsOfUnity (n : ℕ) (v.adicCompletion K) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact rootsOfUnityEquivOfPrimitiveRoots (algebraMap K (v.adicCompletion K)).injective hmu

def sLocalHilbertForm (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalPowerClasses K n S →* (SLocalPowerClasses K n S →* rootsOfUnity (n : ℕ) K) where
  toFun x :=
    { toFun := fun y => ∏ v : S, (sLocalRootEquiv K n hmu v.1).symm
        (finitePlaceAdicHilbertPairingFamily K n hmu v.1 (x v) (y v))
      map_one' := by simp
      map_mul' y z := by simp [Finset.prod_mul_distrib] }
  map_one' := by ext y; simp
  map_mul' x z := by ext y; simp [Finset.prod_mul_distrib]

@[simp] theorem sLocalHilbertForm_apply (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalPowerClasses K n S) :
    sLocalHilbertForm K n hmu S x y = ∏ v : S, (sLocalRootEquiv K n hmu v.1).symm
      (finitePlaceAdicHilbertPairingFamily K n hmu v.1 (x v) (y v)) := rfl

theorem sLocalHilbertForm_skew (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalPowerClasses K n S) :
    sLocalHilbertForm K n hmu S x y = (sLocalHilbertForm K n hmu S y x)⁻¹ := by
  rw [sLocalHilbertForm_apply, sLocalHilbertForm_apply, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [(finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K n hmu v.1).2.1,
    map_inv]

theorem sLocalHilbertForm_mulSingle (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S)
    (v : S) (q : PowerClassGroup (v.1.adicCompletion K) n) :
    sLocalHilbertForm K n hmu S x (Pi.mulSingle v q) =
      (sLocalRootEquiv K n hmu v.1).symm
        (finitePlaceAdicHilbertPairingFamily K n hmu v.1 (x v) q) := by
  rw [sLocalHilbertForm_apply, Finset.prod_eq_single v]
  · simp
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw]
  · simp

theorem sLocalHilbertForm_nondegenerate_left (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S)
    (hx : ∀ y, sLocalHilbertForm K n hmu S x y = 1) : x = 1 := by
  funext v
  apply (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K n hmu v.1).2.2.1.1
  intro q
  have h := hx (Pi.mulSingle v q)
  rw [sLocalHilbertForm_mulSingle] at h
  apply (sLocalRootEquiv K n hmu v.1).symm.injective
  simpa only [map_one] using h

theorem sLocalHilbertForm_nondegenerate_right (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SLocalPowerClasses K n S)
    (hy : ∀ x, sLocalHilbertForm K n hmu S x y = 1) : y = 1 := by
  apply sLocalHilbertForm_nondegenerate_left K n hmu S y
  intro x
  rw [sLocalHilbertForm_skew, hy, inv_one]

theorem sLocalHilbertForm_unitMap (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : SUnitGroup (K := K) S) :
    sLocalHilbertForm K n hmu S (sLocalUnitClassMap K n S a) (sLocalUnitClassMap K n S b) =
      ∏ v : S, globalFinitePlaceHilbertSymbol K n hnK hmu v.1 (a : Kˣ) (b : Kˣ) := by
  rw [sLocalHilbertForm_apply]
  apply Finset.prod_congr rfl
  intro v _
  change GlobalHilbertPairingFamily.finiteFactor K
    (finitePlaceAdicHilbertPairingFamily K n hmu) hmu v.1 (a : Kˣ) (b : Kˣ) = _
  exact finitePlaceAdicHilbertPairingFamily_finiteFactor K n hnK hmu v.1 (a : Kˣ) (b : Kˣ)

variable [NumberField.IsTotallyComplex K]

theorem sLocalHilbertForm_sUnit_isotropic (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S)
    (a b : SUnitGroup (K := K) S) :
    sLocalHilbertForm K n hmu S (sLocalUnitClassMap K n S a) (sLocalUnitClassMap K n S b) = 1 := by
  have h := sUnit_hilbertSProduct_eq_one K n hnK hmu S hS a b
  unfold VaryingKummerAnalytic.probeHilbertSProduct at h
  have hi (v : InfinitePlace K) :
      infinitePlaceHilbertSymbol K n v (a : Kˣ) (b : Kˣ) = 1 :=
    infinitePlaceHilbertSymbol_eq_one_of_isComplex K n v _ _ (NumberField.IsTotallyComplex.isComplex v)
  simp only [hi, Finset.prod_const_one, one_mul] at h
  let e := nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  rw [sLocalHilbertForm_unitMap K n hnK hmu]
  change (∏ v : S, e (finitePlaceHilbertSymbol K n hnK hmu v.1 (a : Kˣ) (b : Kˣ))) = 1
  rw [← map_prod]
  have hp : (∏ v : S, finitePlaceHilbertSymbol K n hnK hmu v.1 (a : Kˣ) (b : Kˣ)) = 1 := by
    exact (Finset.prod_coe_sort S
      (fun v => finitePlaceHilbertSymbol K n hnK hmu v (a : Kˣ) (b : Kˣ))).trans h
  rw [hp, map_one]

theorem sLocalHilbertForm_unitImage_isotropic (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S) :
    ∀ x ∈ sUnitPowerImage K n S, ∀ y ∈ sUnitPowerImage K n S,
      sLocalHilbertForm K n hmu S x y = 1 := by
  rintro x ⟨q, rfl⟩ y ⟨r, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ r
  change sLocalHilbertForm K n hmu S (sLocalUnitClassMap K n S a) (sLocalUnitClassMap K n S b) = 1
  exact sLocalHilbertForm_sUnit_isotropic K n hnK hmu S hS a b

end
end ArtinMatthews
