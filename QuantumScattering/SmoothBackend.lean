/- F2: a genuinely nonconstant, explicitly soluble backend.
The normalized equation is f'' = 2/(1+x^2) * f. Its real fundamental matrix is
[[1+x^2, (x+(1+x^2) arctan x)/2], [2x, 1+x arctan x]].
No ODE solution or scattering theorem is taken as a model input.
This does NOT establish automatic existence for arbitrary continuous potentials.
Uncompiled proof candidates. -/
import QuantumScattering.EvolutionSegment

noncomputable section
namespace QuantumScattering
namespace SmoothBackend

lemma denominator_pos (x : ℝ) : 0<1+x^2 := by positivity
lemma denominator_ne (x : ℝ) : 1+x^2≠0 := ne_of_gt (denominator_pos x)

lemma derivative_a (x : ℝ) : HasDerivAt (fun t:ℝ=>1+t^2) (2*x) x := by
  convert ((hasDerivAt_id x).pow 2).const_add 1 using 1 <;> simp [id, Pi.mul_apply, Pi.pow_apply] <;> ring
lemma derivative_b (x : ℝ) :
    HasDerivAt (fun t:ℝ=>(t+(1+t^2)*Real.arctan t)/2)
      (1+x*Real.arctan x) x := by
  have h := ((hasDerivAt_id x).add ((derivative_a x).mul (Real.hasDerivAt_arctan x))).div_const 2
  convert h using 1
  · rfl
  · field_simp [denominator_ne x]
    ring
lemma derivative_c (x : ℝ) : HasDerivAt (fun t:ℝ=>2*t) 2 x := by
  simpa using (hasDerivAt_id x).const_mul 2
lemma derivative_d (x : ℝ) :
    HasDerivAt (fun t:ℝ=>1+t*Real.arctan t)
      (Real.arctan x+x/(1+x^2)) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).const_add 1 using 1 <;> simp [id, Pi.mul_apply, Pi.pow_apply] <;> ring

/-- Every differential certificate is discharged for the explicit functions. -/
def evolution : RealEvolution where
  coefficient := fun x=> -2/(1+x^2)
  a := fun x=>1+x^2
  b := fun x=>(x+(1+x^2)*Real.arctan x)/2
  c := fun x=>2*x
  d := fun x=>1+x*Real.arctan x
  a_zero := by norm_num
  b_zero := by norm_num
  c_zero := by norm_num
  d_zero := by norm_num
  a_deriv := derivative_a
  b_deriv := derivative_b
  c_deriv := by
    intro x
    convert derivative_c x using 1 <;> field_simp [denominator_ne x] <;> ring
  d_deriv := by
    intro x
    convert derivative_d x using 1 <;> field_simp [denominator_ne x] <;> ring

lemma coefficient_not_constant : evolution.coefficient 0≠evolution.coefficient 1 := by
  norm_num [evolution]

def segment (L : ℝ) (hL : 0<L) (l r : Port) : EvolutionSegment :=
  ⟨evolution,L,hL,l,r⟩

/-- A new, non-piecewise-constant interior solves the same global scattering
contract by calling the generic engine, with no new scattering algebra. -/
theorem smooth_scattering_unique (L : ℝ) (hL : 0<L) (l r : Port) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), (segment L hL l r).Admissible iL iR fv.1 fv.2 :=
  (segment L hL l r).existsUnique_scattering iL iR

/-- Fixing a reference energy E defines this particular physical potential.
This is an exactly soluble family at that design energy, NOT a theorem that
one fixed potential is solved at every energy by this same fundamental matrix. -/
def potential (hbar mass E : ℝ) (s : EvolutionSegment) (x : ℝ) : ℝ :=
  E-hbar^2/(2*mass)*s.coefficient x

lemma potential_inside (hbar mass E L : ℝ) (hL : 0<L) (l r : Port)
    (x : ℝ) (hx : 0<x ∧ x<L) :
    potential hbar mass E (segment L hL l r) x=E+hbar^2/(mass*(1+x^2)) := by
  simp [potential, EvolutionSegment.coefficient, segment, evolution,
    not_lt.mpr (le_of_lt hx.1), hx.2]
  simp [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- Literal physical equation and C1 regularity for the global attached-lead
solution, not merely for its interior fundamental matrix. -/
theorem smooth_physical_solution (hbar mass E L : ℝ) (hh : 0<hbar) (hm : 0<mass)
    (hL : 0<L) (l r : Port) (iL iR : ℂ) :
    let s := segment L hL l r
    ContDiff ℝ 1 (s.wave iL iR) ∧
    (∀ x, x∉s.jumps →
      -(hbar^2/(2*mass):ℝ) • deriv (deriv (s.wave iL iR)) x+
        potential hbar mass E s x • s.wave iL iR x=E • s.wave iL iR x) ∧
    s.channels.scatteringMatrix.conjTranspose*s.channels.scatteringMatrix=1 := by
  dsimp only
  let s := segment L hL l r
  refine ⟨(s.classical (s.initial iL iR)).C1,?_,s.channels.unitary_matrix.1⟩
  intro x hx
  have he : deriv (deriv (s.wave iL iR)) x = -(s.coefficient x : ℂ) * s.wave iL iR x :=
    (s.classical (s.initial iL iR)).second_order x hx
  change -(hbar^2/(2*mass):ℝ) • deriv (deriv (s.wave iL iR)) x +
    potential hbar mass E s x • s.wave iL iR x = E • s.wave iL iR x
  rw [he]
  simp only [potential,Complex.real_smul]
  push_cast
  ring

end SmoothBackend
end QuantumScattering
