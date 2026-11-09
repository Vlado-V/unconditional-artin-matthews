module

public import ArtinMatthews.SourcePrincipalBallFrequencyTransform


set_option backward.privateInPublic true
@[expose] public section

/-! Express the primal ball sum on the original S-integer index, by a
literal ideal membership indicator. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourcePrincipalBallIntegerSet (e : S → ℤ) : Set OS :=
  {x | (x : K) ∈ sourceFiniteBallIdeal K S e}

def sourcePrincipalBallIntegerEquiv (e : S → ℤ) :
    (sourceFiniteBallIdeal K S e).val ≃ sourcePrincipalBallIntegerSet K S₀ e where
  toFun x := ⟨sourcePrincipalBallIdealToInteger K S₀ e x, x.property⟩
  invFun x := ⟨(x.val : K), x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourcePrincipalBallPrimalTerm (e : S → ℤ) (a : OS) (w : OS ⧸ Ideal.span {a} → ℂ)
    (f : CPlaces → 𝓢(ℂ, ℂ)) : OS → ℂ :=
  (sourcePrincipalBallIntegerSet K S₀ e).indicator (fun x =>
    w (Ideal.Quotient.mk _ x) * sourceComplexTensor f (sourceComplexFieldEmbedding K (x : K)))

theorem sourcePrincipalBallWeightedTerm_mk (e : S → ℤ) (M : Ideal (𝓞 K)) (a : OS)
    (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ))
    (x : (sourceFiniteBallIdeal K S e).val) :
    sourcePrincipalBallWeightedTerm K S₀ e M (fun q => w (Ideal.quotEquivOfEq hgen q)) f x =
      w (Ideal.Quotient.mk _ (sourcePrincipalBallIdealToInteger K S₀ e x)) *
        sourceComplexTensor f (sourceComplexFieldEmbedding K (x : K)) := by
  unfold sourcePrincipalBallWeightedTerm
  change w (Ideal.quotEquivOfEq hgen (Ideal.Quotient.mk _
    (sourcePrincipalBallIdealToInteger K S₀ e x))) * _ = _
  rw [Ideal.quotEquivOfEq_mk]

theorem sourcePrincipalBallPrimalTerm_tsum (e : S → ℤ) (M : Ideal (𝓞 K)) (a : OS)
    (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (∑' x, sourcePrincipalBallPrimalTerm K S₀ e a w f x) =
      ∑' x : (sourceFiniteBallIdeal K S e).val,
        sourcePrincipalBallWeightedTerm K S₀ e M (fun q => w (Ideal.quotEquivOfEq hgen q)) f x := by
  unfold sourcePrincipalBallPrimalTerm
  rw [← tsum_subtype]
  refine ((sourcePrincipalBallIntegerEquiv K S₀ e).tsum_eq _).symm.trans ?_
  exact tsum_congr (fun x => (sourcePrincipalBallWeightedTerm_mk K S₀ e M a hgen w f x).symm)

variable [IsTotallyComplex K]

theorem sourcePrincipalBallPrimalTerm_summable_norm (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (a : OS)
    (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    Summable (fun x => ‖sourcePrincipalBallPrimalTerm K S₀ e a w f x‖) := by
  unfold sourcePrincipalBallPrimalTerm
  simp_rw [norm_indicator_eq_indicator_norm]
  apply summable_subtype_iff_indicator.mp
  apply (sourcePrincipalBallIntegerEquiv K S₀ e).summable_iff.mp
  exact (sourcePrincipalBallWeightedTerm_summable_norm K S₀ e M hM hc _ f).congr
    (fun x => congrArg norm (sourcePrincipalBallWeightedTerm_mk K S₀ e M a hgen w f x))

end
end ArtinMatthews.SourcePhysical
