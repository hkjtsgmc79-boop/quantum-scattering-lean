/- F2 framework endpoints. All fields below are conclusions, not input axioms.
The single-layer legacy bridge is a separate compile target to keep the core
library independent of the old rectangular-model implementation.
Candidate source: no kernel validation is claimed in this release. -/
import QuantumScattering.Refinement
import QuantumScattering.Radiation
import QuantumScattering.SmoothBackend

noncomputable section
namespace QuantumScattering

structure ReusableFrameworkCertificate (p : PhysicalProblem) : Prop where
  finite_layers : FiniteScatteringCertificate p
  incoming_infinity : ∀ iL iR:ℂ, ∃! f:ℝ→ℂ, p.problem.IncomingAtInfinity iL iR f
  radiation_equivalence : ∀ iL iR f,
    p.problem.IncomingAtInfinity iL iR f ↔ p.problem.Admissible iL iR f (deriv f)
  arbitrary_current : ∀ f v:ℝ→ℂ,
    ClassicalState p.problem.coefficient p.problem.jumps f v →
    ∀ x, current p.hbar p.mass f x=(p.hbar/p.mass)*(⟨f 0,v 0⟩:State).flux

theorem reusable_finite_layer_framework (p : PhysicalProblem) :
    ReusableFrameworkCertificate p where
  finite_layers := finite_piecewise_real_scattering p
  incoming_infinity := p.problem.existsUnique_incoming_at_infinity
  radiation_equivalence := p.problem.incoming_iff_admissible
  arbitrary_current := fun f v hf x =>
    p.problem.current_arbitrary_classical f v hf p.hbar p.mass x

/-- Scalar physical data and an arbitrary list remain the only model input. -/
theorem any_finite_layers_with_asymptotic_uniqueness
    (hbar mass energy vL vR : ℝ) (layers : List PhysicalLayer)
    (hh : 0<hbar) (hm : 0<mass) (hL : vL<energy) (hR : vR<energy) :
    ReusableFrameworkCertificate ⟨hbar,mass,energy,vL,vR,layers,hh,hm,hL,hR⟩ :=
  reusable_finite_layer_framework _

end QuantumScattering
