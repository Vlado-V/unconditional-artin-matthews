module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! # Field Fourier -/

namespace OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction

noncomputable section

section

/-! Field isomorphisms transport the concrete symplectic and Heisenberg actions. -/

open _root_.Matrix

def fieldCharacter {k l : Type} [Field k] [Field l] (e : k ≃+* l) (ψ : AddChar k ℂ) : AddChar l ℂ :=
  ψ.compAddMonoidHom e.symm.toAddMonoidHom

def fieldSymplecticMap {k l : Type} [Field k] [Field l] (e : k ≃+* l) (n : ℕ) :
    FunctionsMetaplectic.Construction.Symplectic k n →* FunctionsMetaplectic.Construction.Symplectic l n where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e.toRingHom⟩
  map_one' := by apply Subtype.ext; exact Matrix.map_one _ e.map_zero e.map_one
  map_mul' _ _ := by apply Subtype.ext; exact Matrix.map_mul

theorem fieldSymplecticMap_action {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    FunctionsMetaplectic.Construction.symplecticAction (fieldSymplecticMap e n g) (fun i => e (v i)) =
      fun i => e (FunctionsMetaplectic.Construction.symplecticAction g v i) := by
  ext i
  exact (RingHom.map_mulVec e.toRingHom g.val v i).symm

theorem fieldHeisenbergFunction {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergFunction (fieldCharacter e ψ) (fun i => e (v i))
      (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f).val =
      fun x => FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val (fun i => e.symm (x i)) := by
  funext x
  change ψ (e.symm (∑ i, e (v (Sum.inr i)) * (x i - e (v (Sum.inl i)) / 2))) *
    f.val (fun i => e.symm (x i - e (v (Sum.inl i)))) =
      ψ (∑ i, v (Sum.inr i) * (e.symm (x i) - v (Sum.inl i) / 2)) *
        f.val (fun i => e.symm (x i) - v (Sum.inl i))
  simp only [map_sum, map_mul, map_sub, map_div₀, map_ofNat, RingEquiv.symm_apply_apply]

theorem fieldHeisenbergGraph {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph (fieldCharacter e ψ) (fun i => e (v i))
        (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f)
        (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) h) := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [fieldHeisenbergFunction]
  constructor
  · intro hh
    ext x
    exact congrFun hh (fun i => e.symm (x i))
  · intro hh
    ext x
    have ht := congrFun hh (fun i => e (x i))
    change h.val (fun i => e.symm (e (x i))) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val (fun i => e.symm (e (x i))) at ht
    simpa only [RingEquiv.symm_apply_apply] using! ht

end

/-! Transport of the actual product measures and Fourier integrals between field presentations. -/

open _root_.MeasureTheory

variable {k l : Type} [NormedField k] [NormedField l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]

theorem field_productMeasure_map
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hmap : μ.map e = ν) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).map (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) =
      Measure.pi (fun _ : Fin n => ν) := by
  let : SigmaFinite (μ.map e) := hmap.symm ▸ inferInstance
  have hm := Measure.pi_map_pi (μ := fun _ : Fin n => μ) (f := fun _ => e)
    (fun _ => he.measurable.aemeasurable)
  simpa only [hmap] using! hm

theorem field_fourierIntegral
    [SecondCountableTopology k] [SecondCountableTopology l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hmap : μ.map e = ν) (n : ℕ) (ψ : AddChar k ℂ) (f : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (x : FunctionsMetaplectic.Construction.Position l n) :
    FunctionsMetaplectic.Construction.fourierIntegral (fieldCharacter e ψ) (Measure.pi (fun _ : Fin n => ν))
      (fun y => f (fun i => e.symm (y i))) x =
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (fun i => e.symm (x i)) := by
  let E := FieldCoordinates.Construction.fieldPositionEquiv e he he' n
  have hi := integral_map_equiv (μ := Measure.pi (fun _ : Fin n => μ))
    E.toHomeomorph.toMeasurableEquiv
      (fun y => f (E.symm y) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x y))
  have hm := field_productMeasure_map e he he' μ ν hmap n
  change (Measure.pi (fun _ : Fin n => μ)).map E.toHomeomorph.toMeasurableEquiv =
    Measure.pi (fun _ : Fin n => ν) at hm
  rw [hm] at hi
  change (∫ y, f (fun i => e.symm (y i)) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x y)
      ∂Measure.pi (fun _ : Fin n => ν)) =
    ∫ y, f (fun i => e.symm (e (y i))) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x (fun i => e (y i)))
      ∂Measure.pi (fun _ : Fin n => μ) at hi
  rw [FunctionsMetaplectic.Construction.fourierIntegral, hi, FunctionsMetaplectic.Construction.fourierIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [RingEquiv.symm_apply_apply]
    congr 1
    change ψ (e.symm (-∑ i, x i * e (y i))) = ψ (-∑ i, e.symm (x i) * y i)
    rw [map_neg, map_sum]
    simp only [map_mul, RingEquiv.symm_apply_apply]

end

end OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction
