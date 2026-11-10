module

public import ArtinMatthews.SourceKPLocalCompactProductLift
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedProjection
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

/-! A retained slice keeps its exterior remainder and changes a single
actual local lift. Deleting that slot gives a remainder with identity
base at the same place, as required for its upper-root covariance. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (places : Finset (HeightOneSpectrum (𝓞 K)))

local notation "G" => SourceKPAdelicProjective K hζ
local notation "G∞" => PGL(2, InfiniteAdeleRing K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "G₀" => (fun Q : ↥places => SourceFiniteKP2Projective K hζ (Subtype.val Q))
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ
local notation "L" => sourceKPLocalCompactProductLift K hζ places
local notation "base" => sourceKPAdelicLocalBase K hζ

theorem sourceKPAdelicOutgoingRetainedLift_arch_one (g : Gₛ) : (L g).1 = 1 := by
  let a : Gₛ →* G∞ := (MonoidHom.fst G∞ Gf).comp L
  have ha : a = 1 := by
    apply MonoidHom.pi_ext
    intro P x
    change (L (Pi.mulSingle (M := G₀) P x)).1 = 1
    rw [sourceKPAdelicOutgoingRetainedLift_single K hζ places P x]
    rfl
  exact congrArg (fun a : Gₛ →* G∞ => a g) ha

theorem sourceKPAdelicOutgoingRetainedLift_update (g : Gₛ) (P : ↥places) (x : G₀ P) :
    L (Function.update g P x) = L (Function.update g P (1 : G₀ P)) * ι₀ P.val x := by
  have h₁ := Pi.update_eq_div_mul_mulSingle (i := P) g (1 : G₀ P)
  rw [Pi.mulSingle_one, mul_one] at h₁
  rw [Pi.update_eq_div_mul_mulSingle (i := P) g x, ← h₁, map_mul L,
    sourceKPAdelicOutgoingRetainedLift_single K hζ places P x]

def sourceKPAdelicOutgoingRetainedSliceRest (qf : Gf) (g : Gₛ) (P : ↥places) : Gf :=
  qf * (L (Function.update g P (1 : G₀ P))).2

local notation "rest" => sourceKPAdelicOutgoingRetainedSliceRest K hζ places

theorem sourceKPAdelicOutgoingRetainedSliceRest_mul_local (qf : Gf) (g : Gₛ)
    (P : ↥places) (x : G₀ P) :
    qf * (L (Function.update g P x)).2 = rest qf g P * (ι₀ P.val x).2 := by
  have he := congrArg (fun u : G => u.2)
    (sourceKPAdelicOutgoingRetainedLift_update K hζ places g P x)
  change (L (Function.update g P x)).2 =
    (L (Function.update g P (1 : G₀ P))).2 * (ι₀ P.val x).2 at he
  rw [he, sourceKPAdelicOutgoingRetainedSliceRest, mul_assoc]

theorem sourceKPAdelicOutgoingRetainedSliceRest_base_one (qf : Gf) (g : Gₛ)
    (P : ↥places) (hqf : base P.val (1,qf) = 1) : base P.val (1,rest qf g P) = 1 := by
  let g₀ := Function.update g P (1 : G₀ P)
  have he : ((1,rest qf g P) : G) = ((1,qf) : G) * L g₀ := by
    apply Prod.ext
    · change (1 : G∞) = 1 * (L g₀).1
      rw [sourceKPAdelicOutgoingRetainedLift_arch_one K hζ places, one_mul]
    · rfl
  rw [he, map_mul (base P.val), hqf, sourceKPAdelicOutgoingRetainedLift_localBase K hζ places]
  change 1 * sourceFiniteKP2ProjectiveProjection K hζ P.val (Function.update g P (1 : G₀ P) P) = 1
  rw [Function.update_self, map_one, one_mul]

end
end ArtinMatthews
