module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi
public import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators
public import OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration


set_option backward.privateInPublic true
@[expose] public section

/-! # Graph Reduction -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.GraphReduction.Construction

noncomputable section

/-! Algebraic completion criteria for the rational graph.
Existence of a Fourier family and triviality above the identity remain
explicit hypotheses of these reductions; the module does not assert them. -/

theorem subgroup_graph_realization
    {A B : Type*} [Group A] [Group B] (R : Subgroup (A × B))
    (htotal : ∀ a, ∃ b, (a, b) ∈ R)
    (hid : ∀ b, (1, b) ∈ R → b = 1) :
    ∃ s : A →* B, ∀ a b, (a, b) ∈ R ↔ s a = b := by
  have huniq (a : A) (b c : B) (hb : (a, b) ∈ R) (hc : (a, c) ∈ R) : b = c := by
    have h := R.mul_mem (R.inv_mem hb) hc
    change (a⁻¹ * a, b⁻¹ * c) ∈ R at h
    rw [inv_mul_cancel] at h
    exact inv_mul_eq_one.mp (hid _ h)
  choose f hf using htotal
  let s : A →* B :=
    { toFun := f
      map_one' := hid _ (hf 1)
      map_mul' := fun a b => huniq (a * b) _ _ (hf (a * b)) (R.mul_mem (hf a) (hf b)) }
  refine ⟨s, ?_⟩
  intro a b
  constructor
  · exact huniq a (f a) b (hf a)
  · intro h
    exact h ▸ hf a

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def rationalGraphDomain : Subgroup (Local.FunctionsMetaplectic.Construction.Symplectic F N) :=
  (Rational.Construction.rationalGraph F N ψ).map (MonoidHom.fst _ _)

theorem mem_rationalGraphDomain (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    γ ∈ rationalGraphDomain F N ψ ↔ ∃ a, (γ, a) ∈ Rational.Construction.rationalGraph F N ψ := by
  constructor
  · rintro ⟨⟨γ', a⟩, ha, he⟩
    change γ' = γ at he
    subst γ'
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(γ, a), ha, rfl⟩

theorem rationalGraphDomain_contains_levi (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    Local.Generators.Construction.leviSymplectic A ∈ rationalGraphDomain F N ψ :=
  (mem_rationalGraphDomain F N ψ _).mpr ⟨_, NormalizationLevi.Construction.rationalLeviLift_mem_graph F N ψ A⟩

/-- Totality reduces to existence of the remaining prescribed generator
families. The Levi families have already been constructed unconditionally. -/
theorem rationalGraph_total_of_generator_families
    (hQ : ∀ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N, ∃ a, Rational.Construction.IsRationalQuadratic F N ψ B a)
    (hW : ∃ a, Rational.Construction.IsRationalFourier F N ψ a) :
    ∀ γ : Local.FunctionsMetaplectic.Construction.Symplectic F N, ∃ a, (γ, a) ∈ Rational.Construction.rationalGraph F N ψ := by
  let R := rationalGraphDomain F N ψ
  have hq : ∀ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N, Local.Generators.Construction.quadraticSymplectic B ∈ R := by
    intro B
    obtain ⟨a, ha⟩ := hQ B
    apply (mem_rationalGraphDomain F N ψ _).mpr
    exact ⟨_, Subgroup.subset_closure (Or.inr (Or.inl ⟨B, a, ha, rfl⟩))⟩
  have hw : SymplecticGeneration.weyl (k := F) (N := N) ∈ R := by
    obtain ⟨a, ha⟩ := hW
    apply (mem_rationalGraphDomain F N ψ _).mpr
    exact ⟨_, Subgroup.subset_closure (Or.inr (Or.inr ⟨a, ha, rfl⟩))⟩
  have hu : ∀ (B : Matrix (Fin N) (Fin N) F) (hB : B.IsSymm),
      SymplecticGeneration.upper B hB ∈ R := by
    intro B hB
    have h := R.mul_mem (R.mul_mem (R.inv_mem hw) (hq ⟨-B, hB.neg⟩)) hw
    change SymplecticGeneration.weyl⁻¹ *
      SymplecticGeneration.lower (-B) hB.neg *
      SymplecticGeneration.weyl ∈ R at h
    rw [SymplecticGeneration.lower_conjugation] at h
    simpa only [neg_neg, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  have ht : R = ⊤ := SymplecticGeneration.subgroup_eq_top_of_generators R hu
    (rationalGraphDomain_contains_levi F N ψ) hw
  intro γ
  apply (mem_rationalGraphDomain F N ψ γ).mp
  change γ ∈ R
  rw [ht]
  trivial

theorem rationalGraph_total_of_fourier_family
    (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (hW : ∃ a, Rational.Construction.IsRationalFourier F N ψ a) :
    ∀ γ : Local.FunctionsMetaplectic.Construction.Symplectic F N, ∃ a, (γ, a) ∈ Rational.Construction.rationalGraph F N ψ :=
  rationalGraph_total_of_generator_families F N ψ
    (fun B => ⟨QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B,
      QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc B⟩) hW

/-- Once scalar relations above the identity are proved trivial, totality
produces the canonical rational homomorphism and its covering equation. -/
theorem rationalGraph_realization_of_total_and_identity_fiber
    (htotal : ∀ γ : Local.FunctionsMetaplectic.Construction.Symplectic F N, ∃ a, (γ, a) ∈ Rational.Construction.rationalGraph F N ψ)
    (hid : ∀ a : Vacuum.Construction.GlobalCover F N ψ, (1, a) ∈ Rational.Construction.rationalGraph F N ψ → a = 1) :
    ∃ r : Local.FunctionsMetaplectic.Construction.Symplectic F N →* Vacuum.Construction.GlobalCover F N ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F N ψ ↔ r γ = a) ∧
      ∀ γ, Vacuum.Construction.globalProjection F N ψ (r γ) = Vacuum.Construction.rationalSymplectic F N γ := by
  obtain ⟨r, hr⟩ := subgroup_graph_realization (Rational.Construction.rationalGraph F N ψ) htotal hid
  refine ⟨r, hr, ?_⟩
  intro γ
  exact Rational.Construction.rationalGraph_covers F N ψ ((hr γ (r γ)).mpr rfl)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.GraphReduction.Construction
