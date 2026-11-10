module

public import ArtinMatthews.SLocalWeakApproximation
public import ArtinMatthews.SLocalSixthUnitImage
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual product of all S-local multiplicative groups, including
every infinite completion, modulo its nth powers. In a totally complex
field the archimedean power classes are proved trivial, giving the
canonical equivalence with the finite-place power-class product. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open GlobalClassFieldTheory.ClassFieldAxiom
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev SWholeUnits (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : InfinitePlace K, w.Completionˣ) × (∀ v : S, (v.1.adicCompletion K)ˣ)

abbrev SWholePowerClasses (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  SWholeUnits K S ⧸ (powMonoidHom (n : ℕ) : SWholeUnits K S →* SWholeUnits K S).range

def sWholeDiagonal (S : Finset (HeightOneSpectrum (𝓞 K))) : Kˣ →* SWholeUnits K S :=
  (MonoidHom.pi fun w : InfinitePlace K => Units.map (algebraMap K w.Completion).toMonoidHom).prod
    (MonoidHom.pi fun v : S => Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom)

def sWholeGlobalClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →* SWholePowerClasses K n S := (QuotientGroup.mk' _).comp (sWholeDiagonal K S)

def sWholeUnitPowerImage (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SWholePowerClasses K n S) :=
  ((sWholeGlobalClassMap K n S).comp (SUnitGroup (K := K) S).subtype).range

def sFinitePowerEquiv (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((∀ v : S, (v.1.adicCompletion K)ˣ) ⧸ (powMonoidHom (n : ℕ)).range) ≃*
      SLocalPowerClasses K n S := by
  unfold SLocalPowerClasses PowerClassGroup
  exact QuotientGroup.mulEquivPiModRangePowMonoidHom (fun v : S => (v.1.adicCompletion K)ˣ) (n : ℕ)

variable [NumberField.IsTotallyComplex K]

omit [NumberField K] in
theorem sArchPowerClasses_subsingleton (n : ℕ+) :
    Subsingleton (∀ w : InfinitePlace K,
      w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) := by
  let : ∀ w : InfinitePlace K, Subsingleton
      (w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) := fun w => by
    have hw : ¬ w.IsReal :=
      InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
    have hpower : (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range = ⊤ := by
      rw [nthPowerSubgroup_eq_infinitePositiveSubgroup n w (Or.inr hw)]
      ext x
      simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
    rw [hpower]
    exact QuotientGroup.subsingleton_quotient_top
  infer_instance

def sWholePowerEquiv (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SWholePowerClasses K n S ≃* SLocalPowerClasses K n S := by
  let e₀ := LocalFieldTheory.nthPowerProductQuotientEquiv
    (∀ w : InfinitePlace K, w.Completionˣ) (∀ v : S, (v.1.adicCompletion K)ˣ) (n : ℕ)
  let e₁ := e₀.trans (MulEquiv.prodCongr
    (QuotientGroup.mulEquivPiModRangePowMonoidHom (fun w : InfinitePlace K => w.Completionˣ) (n : ℕ))
    (sFinitePowerEquiv K n S))
  let : Subsingleton (∀ w : InfinitePlace K,
      w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) :=
    sArchPowerClasses_subsingleton K n
  let e₂ : ((∀ w : InfinitePlace K,
      w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) ×
        SLocalPowerClasses K n S) ≃* SLocalPowerClasses K n S :=
    { toFun := Prod.snd
      invFun := fun x => (1, x)
      left_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact e₁.trans e₂

@[simp] theorem sWholePowerEquiv_mk (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SWholeUnits K S) :
    sWholePowerEquiv K n S (QuotientGroup.mk' _ x) =
      fun v : S => powerClass (v.1.adicCompletion K) n (x.2 v) := rfl

@[simp] theorem sWholePowerEquiv_globalClass (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    sWholePowerEquiv K n S (sWholeGlobalClassMap K n S a) = sLocalGlobalClassMap K n S a := rfl

theorem sWholePowerEquiv_unitImage_iff (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SWholePowerClasses K n S) :
    x ∈ sWholeUnitPowerImage K n S ↔ sWholePowerEquiv K n S x ∈ sUnitPowerImage K n S := by
  constructor
  · rintro ⟨u, rfl⟩
    change sWholePowerEquiv K n S (sWholeGlobalClassMap K n S (u : Kˣ)) ∈ _
    rw [sWholePowerEquiv_globalClass, sLocalGlobalClassMap_sUnit]
    exact (mem_sUnitPowerImage_iff_unitClass K n S _).mpr ⟨u, rfl⟩
  · intro hx
    obtain ⟨u, hu⟩ := (mem_sUnitPowerImage_iff_unitClass K n S _).mp hx
    refine ⟨u, ?_⟩
    change sWholeGlobalClassMap K n S (u : Kˣ) = x
    apply (sWholePowerEquiv K n S).injective
    rw [sWholePowerEquiv_globalClass, sLocalGlobalClassMap_sUnit]
    exact hu

def sWholeHilbertForm (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SWholePowerClasses K n S →* (SWholePowerClasses K n S →* rootsOfUnity (n : ℕ) K) :=
  ((MonoidHom.compHom' (M := SWholePowerClasses K n S) (N := SLocalPowerClasses K n S)
      (P := rootsOfUnity (n : ℕ) K)) (sWholePowerEquiv K n S).toMonoidHom).comp
    ((sLocalHilbertForm K n hmu S).comp (sWholePowerEquiv K n S).toMonoidHom)

@[simp] theorem sWholeHilbertForm_apply (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SWholePowerClasses K n S) :
    sWholeHilbertForm K n hmu S x y = sLocalHilbertForm K n hmu S
      (sWholePowerEquiv K n S x) (sWholePowerEquiv K n S y) := rfl

end
end ArtinMatthews
