module

public import ArtinMatthews.SourceArchGlobalUpperDerivative
public import ArtinMatthews.SourceArchGlobalDiagonalDerivative


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchGlobalUpperTranslate (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) (t : ℝ) : ℂ :=
  f (q * sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z)))

def sourceArchGlobalDiagonalTranslate (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (t : ℝ) : ℂ :=
  f (q * sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t))

def sourceArchGlobalCasimir (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) : ℂ :=
  -(deriv (deriv (sourceArchGlobalUpperTranslate K hζ f q v 1)) 0 +
    deriv (deriv (sourceArchGlobalUpperTranslate K hζ f q v Complex.I)) 0 +
    deriv (deriv (sourceArchGlobalDiagonalTranslate K hζ f q v)) 0 -
    2 * deriv (sourceArchGlobalDiagonalTranslate K hζ f q v) 0)

theorem sourceArchGlobalUpperTranslate_compactScalar (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) :
    sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v z =
      sourceArchGlobalUpperSection K hζ s q v z := rfl

theorem sourceArchGlobalDiagonalTranslate_compactScalar (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v =
      sourceArchGlobalDiagonalSection K hζ s q v := rfl

end
end ArtinMatthews
