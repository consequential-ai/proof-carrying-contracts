import { Arrow } from '@/components/site-chrome';
import { SiteLink } from '@/components/site-link';
import { experimentSummary } from '@/lib/experiments';

export function ExperimentPreview() {
  const ungated = experimentSummary('procurement', 'ungated');
  const pc2 = experimentSummary('procurement', 'pc2');
  const logistics = experimentSummary('logistics', 'pc2');
  return <section className="v2-section shell experiment-preview" id="experiments" aria-labelledby="experiments-title">
    <div className="section-intro">
      <p className="eyebrow">Evidence</p>
      <h2 id="experiments-title">Procurement and logistics experiments</h2>
      <p>We tested four model configurations on two simulated tasks: paying supplier invoices and dispatching
        refrigerated cargo. Each instance was run with ungated tools and with PC2. We recorded violations,
        task completion and API costs calculated from recorded token usage.</p>
    </div>
    <p className="experiment-scope">Supplier payments</p>
    <dl className="experiment-statistics">
      <div><dt>Ungated runs with violations</dt><dd>{100 * ungated.violations / ungated.runs}<span>%</span></dd></div>
      <div><dt>PC2 runs with violations</dt><dd>{100 * pc2.violations / pc2.runs}<span>%</span></dd></div>
      <div><dt>PC2 runs completed safely</dt><dd>{100 * pc2.completed / pc2.runs}<span>%</span></dd></div>
    </dl>
    <p className="experiment-preview-note">For cargo delivery, PC2 completed {100 * logistics.completed / logistics.runs}% of tasks safely;
      the remaining runs never began cargo operations. The full results report safety, completion and API costs separately.</p>
    <SiteLink className="primary-link" href="/experiments">Read the evidence <Arrow /></SiteLink>
  </section>;
}
