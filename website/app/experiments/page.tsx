import { SiteHeader, SiteFooter, Arrow } from '@/components/site-chrome';
import { SiteLink } from '@/components/site-link';
import { pageMetadata } from '@/lib/site-data';
import { experimentSummary } from '@/lib/experiments';
import automationbench from '@/lib/automationbench-results.json';

export const metadata = pageMetadata('Evidence | Proof Carrying Contracts',
  'Studies of how AI agents work when every consequential action must carry a checked proof: business operations on AutomationBench, and supplier payments and cargo delivery.', '/experiments');

type Measure = { label: string; ungated: number; pc2: number };

function Measures({ items, scope }: { items: Measure[]; scope: string }) {
  return <>
    <dl className="evidence-stats">
      {items.map(item => <div key={item.label}>
        <dt>{item.label}</dt>
        <dd>
          <span className="evidence-value base"><b>{item.ungated}%</b><small>Ungated tools</small></span>
          <span className="evidence-value pc2"><b>{item.pc2}%</b><small>With PC2</small></span>
        </dd>
      </div>)}
    </dl>
    <p className="evidence-scope">{scope}</p>
  </>;
}

function share(part: number, whole: number) {
  return Math.round(100 * part / whole);
}

export default function Evidence() {
  const ab = automationbench.perTask;
  const families = ['procurement', 'logistics'] as const;
  const operational = (arm: 'ungated' | 'pc2') => families.map(family => experimentSummary(family, arm))
    .reduce((total, row) => ({ runs: total.runs + row.runs, violations: total.violations + row.violations, completed: total.completed + row.completed }),
      { runs: 0, violations: 0, completed: 0 });
  const ungated = operational('ungated');
  const pc2 = operational('pc2');
  return <><SiteHeader active="experiments" /><main id="main" className="v2 experiments-page evidence-index">
    <section className="v2-page-opening shell" id="top" aria-labelledby="evidence-heading">
      <div className="reading-column">
        <p className="eyebrow">Evidence</p>
        <h1 id="evidence-heading">PC2 in practice</h1>
        <p className="lead">PC2 lets an agent act only when a checked proof shows that the action keeps to its
          contract. Whether agents can still do useful work under that requirement is an empirical question, and
          these studies measure it.</p>
        <p>Each study runs the same agent on the same tasks twice: with ordinary, ungated tools, and with PC2, where
          every email, payment or other consequential action must carry a proof that Lean checks before the action
          runs. We report safety and completion separately, since avoiding violations is worth little if the work is
          left unfinished.</p>
      </div>
    </section>

    <section className="v2-section shell evidence-list" aria-labelledby="studies-title">
      <h2 id="studies-title" className="sr-only">Studies</h2>

      <article className="evidence-card" aria-labelledby="study-automationbench">
        <p className="eyebrow">Public benchmark · Business operations</p>
        <h3 id="study-automationbench"><SiteLink href="/experiments/automationbench">Testing PC2 on AutomationBench</SiteLink></h3>
        <p>OpenAI’s GPT-6 Astra on AutomationBench tasks it had failed with ungated tools, from ad campaign alerts to
          leave balance reconciliation, carried out in simulated Gmail, Slack, Google Sheets and Google Drive. With PC2
          the agent broke no rule and completed more of the work safely. Refusals often sent it back to records it had
          skipped, and on tasks with no correct ending it stopped and explained why.</p>
        <Measures scope="Share of nine tasks; a task counts when at least two of its three runs had the outcome." items={[
          { label: 'Tasks with a rule broken', ungated: share(ab.violation.baseline, ab.tasks), pc2: share(ab.violation.pc2, ab.tasks) },
          { label: 'Tasks completed safely', ungated: share(ab.safeComplete.baseline, ab.tasks), pc2: share(ab.safeComplete.pc2, ab.tasks) },
        ]} />
        <SiteLink className="primary-link" href="/experiments/automationbench">Read the study <Arrow /></SiteLink>
      </article>

      <article className="evidence-card" aria-labelledby="study-operational">
        <p className="eyebrow">Designed tasks · Payments and logistics</p>
        <h3 id="study-operational"><SiteLink href="/experiments/payments-and-cargo">Testing PC2 on payments and cargo delivery</SiteLink></h3>
        <p>Four models, Luna, Terra, Sol and Astra, on two simulated assignments built around failures seen in earlier
          experiments: authorising supplier payments from a spreadsheet whose importer swaps fields, and delivering
          refrigerated cargo through a private terminal. No PC2 run recorded a violation, while completion and API cost
          depended on the model and the task.</p>
        <Measures scope={`Share of ${ungated.runs} runs per condition across both assignments and all four models.`} items={[
          { label: 'Runs with a violation', ungated: share(ungated.violations, ungated.runs), pc2: share(pc2.violations, pc2.runs) },
          { label: 'Runs completed safely', ungated: share(ungated.completed, ungated.runs), pc2: share(pc2.completed, pc2.runs) },
        ]} />
        <SiteLink className="primary-link" href="/experiments/payments-and-cargo">Read the study <Arrow /></SiteLink>
      </article>
    </section>

    <section className="v2-section shell">
      <SiteLink className="text-link experiment-back-link" href="/overview#research">Read about the research programme <Arrow /></SiteLink>
    </section>
  </main><SiteFooter /></>;
}
