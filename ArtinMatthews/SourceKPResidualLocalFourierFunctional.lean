module

public import ArtinMatthews.SourceKPResidualLocalFourierFunctionalCore
public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber
public import ArtinMatthews.SourceKPCuspResidualLocalUpper
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! The actual local residue functional transforms by the positive
Whittaker character on its full cyclic span. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

private theorem finsupp_linear_ext {A E : Type*} [AddCommGroup E] [Module ℂ E]
    (q : (A →₀ ℂ) →ₗ[ℂ] E) (hs : Function.Surjective q)
    (L R : E →ₗ[ℂ] ℂ) (h : ∀ g, L (q (Finsupp.single g 1)) = R (q (Finsupp.single g 1))) :
    L = R := by
  have heq : L.comp q = R.comp q := by
    apply Finsupp.lhom_ext
    intro g b
    have hb : Finsupp.single g b = b • Finsupp.single g (1 : ℂ) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    simp only [hb,LinearMap.comp_apply,map_smul,h]
  apply LinearMap.ext
  intro f
  obtain ⟨l,rfl⟩ := hs f
  exact congrArg (fun A : (A →₀ ℂ) →ₗ[ℂ] ℂ => A l) heq

private theorem restricted_action_mul {G E : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (C : Submodule ℂ E)
    (hC : ∀ (g : G) (v : E), v ∈ C → ρ g v ∈ C) (a b : G) (v : C) :
    (ρ a).restrict (hC a) ((ρ b).restrict (hC b) v) = (ρ (a*b)).restrict (hC (a*b)) v := by
  apply Subtype.ext
  change ρ a (ρ b v.val) = ρ (a*b) v.val
  rw [map_mul,Module.End.mul_apply]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "L" => P.adicCompletion K
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "s₀" => (1 / 6 : ℂ)
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S s₀ hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "π₀" => sourceAlgebraicInducedRepresentation B₀ ρ₀
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "r₀" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "τ" => fun g : G => Prod.snd (ι₀ g)
local notation "N" => fun x : L => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)
local notation "ψ" => localFiniteCharacter K P

local instance sourceKPResidualLocalFourierUpperValueAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

local notation "gen" => sourceKPResidualLocalFourierGeneratorMap K hζ P hs
local notation "ℓ₀" => sourceKPResidualLocalFourierFunctional K hζ P hs

theorem sourceKPResidualLocalFourierFunctional_upper {T : ℝ} (hT : 2 < T) (qf : Gf)
    (hqf : sourceKPAdelicLocalBase K hζ P (1,qf) = 1) (x : L) (f : C) :
    ℓ₀ hT qf (r₀ (N x) f) = ψ x * ℓ₀ hT qf f := by
  let ℓ := ℓ₀ hT qf
  have hgen (g : G) : ℓ (r₀ (N x * g) v₀) = ψ x * ℓ (r₀ g v₀) := by
    let a (g : G) := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (qf * τ g)
    calc
      _ = a (N x * g) := sourceKPResidualLocalFourierFunctional_generator K hζ P hs hT qf (N x * g)
      _ = ψ x * a g := by
        simpa only [a,sourceKPTraceJacquetFrequencyAt,map_one,
          Units.val_one,one_mul] using
          sourceKPCuspResidualFourierValue_local_upper K hζ P 1 (one_le_two.trans hT.le) qf hqf g x
      _ = _ := congrArg (ψ x * ·)
        (sourceKPResidualLocalFourierFunctional_generator K hζ P hs hT qf g).symm
  let left : C →ₗ[ℂ] ℂ := ℓ.comp (r₀ (N x))
  let right : C →ₗ[ℂ] ℂ := ψ x • ℓ
  have hunit (g : G) : left (gen (Finsupp.single g (1 : ℂ))) =
      right (gen (Finsupp.single g (1 : ℂ))) := by
    have hsingle : gen (Finsupp.single g (1 : ℂ)) = r₀ g v₀ := by
      simp only [sourceKPResidualLocalFourierGeneratorMap,Finsupp.linearCombination_single,one_smul]
    have hright : r₀ (N x) (r₀ g v₀) = r₀ (N x * g) v₀ :=
      restricted_action_mul π₀ C hC (N x) g v₀
    have hv : left (r₀ g v₀) = right (r₀ g v₀) :=
      (congrArg ℓ hright).trans (hgen g)
    exact (congrArg left hsingle).trans (hv.trans (congrArg right hsingle).symm)
  have heq : left = right := finsupp_linear_ext (A := G) (E := C) gen
    (sourceKPResidualLocalFourierGenerators_surjective K hζ P hs) left right hunit
  exact congrArg (fun A : C →ₗ[ℂ] ℂ => A f) heq

end
end ArtinMatthews
