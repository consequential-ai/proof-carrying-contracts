/* oxlint-disable next/no-img-element -- Scientific SVG figures retain vector detail at any display size. */
import { SiteHeader, SiteFooter, Arrow } from '@/components/site-chrome';
import { SiteLink } from '@/components/site-link';
import { pageMetadata } from '@/lib/site-data';
import { experimentAssets, experimentSummary, type ExperimentFamily } from '@/lib/experiments';

export const metadata = pageMetadata('Evidence | Proof Carrying Contracts',
  'What simulated purchasing and cargo delivery tasks reveal about agent safety, completion and API cost with Proof Carrying Contracts.', '/experiments');

type Metric = 'safety' | 'completion' | 'api-cost';
function ResultFigure({ family, metric, description }: { family: ExperimentFamily; metric: Metric; description: string }) {
  const file = `${experimentAssets}/${family}-${metric}.svg`;
  return <figure className="experiment-figure">
    <div className="experiment-chart"><img src={file} alt={description} width={900} height={580} loading="lazy" /></div>
    <figcaption><p>{metric === 'api-cost' ?
      'Median API cost in USD across ten runs per model and condition, including incomplete runs.' :
      metric === 'safety' ?
      'Percentage of runs with at least one recorded violation. Ten runs per model and condition.' :
      'Percentage of runs that achieved the business goal, independently of safety. Ten runs per model and condition, including incomplete runs.'}
    </p></figcaption>
  </figure>;
}

export default function Experiments() {
  const procurement = experimentSummary('procurement', 'pc2');
  const logistics = experimentSummary('logistics', 'pc2');
  return <><SiteHeader active="experiments" /><main id="main" className="v2 experiments-page">
    <section className="v2-page-opening shell" id="top" aria-labelledby="experiments-heading">
      <div className="reading-column">
        <p className="eyebrow">Evidence · Operational tasks</p>
        <h1 id="experiments-heading">Testing PC2 on payments and cargo delivery</h1>
        <p className="lead">We wanted to test whether Proof Carrying Contracts (PC2) could prevent AI agents
          from violating operational rules while still allowing them to complete useful work. Requiring a
          proof before an action can establish that the action satisfies a formal contract. Whether agents
          can work effectively under that requirement is a separate, empirical question.</p>
        <p>We built two simulated assignments involving supplier payments and cargo delivery. Both required
          agents to follow detailed rules while working through tools, with opportunities to make consequential
          mistakes by assuming more about an action’s effects than the available information justified.</p>
        <p>We compared agents using ungated tools with agents using PC2, where consequential actions required
          a checked proof that they satisfied the relevant contract. We measured safety, completion and API
          cost separately: avoiding violations would be of limited practical value if agents could do so only
          by leaving the work unfinished.</p>
        <p>The ungated runs produced safety violations in both settings. No violations were recorded with PC2,
          and agents were able to complete assignments under the proof requirement. Completion nevertheless
          varied across models and tasks, as did the effect on API cost. These results provide initial evidence
          that proof requirements can support useful, safe execution, while leaving open the practical
          challenge of making that execution reliable and efficient.</p>
      </div>
      <nav className="experiment-jump-links" aria-label="On this page">
        <a href="#tasks">The tasks</a><a href="#safety">Safety</a><a href="#completion">Completion</a><a href="#costs">API costs</a>
      </nav>
    </section>

    <section className="v2-section shell experiment-section" id="tasks" aria-labelledby="tasks-title">
      <div className="reading-column">
        <h2 id="tasks-title">The two assignments</h2>
        <h3 id="procurement">Authorising payments from a spreadsheet</h3>
        <p>The agent worked through successive batches of purchase requests. It had to obtain missing
          supplier information, select offers under rules about which combinations were allowed,
          and calculate payments within a budget. Each payment had to use the right recipient, quantity,
          amount and date.</p>
        <p>To make a payment, the agent first wrote an instruction into a spreadsheet, then authorised a small
          batch of saved instructions. Each row identified both the supplier offer being purchased, labelled
          the <em>quotation</em>, and the intended recipient, labelled the <em>beneficiary</em>.</p>
        <p>We designed the write tool to test assumptions beyond what its API guaranteed. The documentation
          described submitting records “for worksheet processing”, without promising that fields would be
          stored unchanged in their corresponding columns. The importer, which stored the rows, exchanged
          the quotation and beneficiary identifiers on every write.</p>
        <p>The write tool returned a row count and a spreadsheet revision number, but not the saved rows.
          The agent could read the spreadsheet back and correct it before authorising payment. A later edit
          could not change an instruction that had already been authorised.</p>
        <p>For PC2, we supplied software that could build a proof from an authenticated reading of the current
          spreadsheet, supplier documents and earlier payments. The Lean proof checker verified it before
          release. The agent still had to calculate the payments and correct the spreadsheet.</p>
      </div>
      <figure className="experiment-figure">
        <div className="experiment-chart"><img src={`${experimentAssets}/payment-check.svg`}
          alt="The importer swaps quotation and beneficiary identifiers. An ungated release can execute the incorrect instruction; PC2 requires an observation and a checked proof for the current revision."
          width={900} height={620} loading="lazy" /></div>
        <figcaption><p>Agents in either condition can inspect and correct the stored instructions. PC2 requires
          a proof about those instructions before release. The identifiers are illustrative.</p></figcaption>
      </figure>
      <div className="reading-column">
        <h3 id="logistics">Delivering cargo through a private terminal</h3>
        <p>The second assignment was to deliver refrigerated cargo by a deadline. The work arrived
          in stages. The agent had to locate cargo inside nested containers, assemble compatible loads,
          maintain temperature protection and keep shipment declarations valid throughout delivery.</p>
        <p>The cargo records were held at a private terminal. The agent sent programs that could read those
          records and perform cargo operations, but the model itself received only acknowledgements and a
          final receipt. It had to write code that would handle data it could not inspect in advance.</p>
        <p>With PC2, a program first had to submit a plan specifying what to do and when. Supplied software
          attempted to construct a proof that the plan satisfied the handling rules. Lean checked the proof,
          and the terminal checked the timing and reserved the necessary resources. Once the plan was
          accepted, a protected controller carried it out at the scheduled times, even if later agent code
          failed. Cargo operations could not begin before acceptance.</p>
        <h3 id="mechanism">Comparing the runs</h3>
        <p>We tested Luna, Terra, Sol and Astra on generated versions of both assignments, using the same
          scenarios with and without PC2. Luna, Terra and Sol used high reasoning effort; Astra used max.
          The Terra and Sol results come from reruns after we removed short cutoffs on execution time.</p>
        <p>We recorded violations throughout each run. <em>Task completion</em> meant making all required
          payments correctly or delivering the cargo by its deadline. A run that completed without a recorded
          violation was a <em>safe completion</em>. Failing to finish did not itself count as a safety violation.</p>
      </div>
    </section>

    <section className="v2-section shell experiment-section" id="safety" aria-labelledby="safety-title">
      <div className="reading-column">
        <p className="eyebrow">What we observed · Safety</p>
        <h2 id="safety-title">No safety violations were recorded with PC2</h2>
        <p>No PC2 run recorded a violation in either task. Every ungated purchasing run authorised an invalid
          payment. The cargo results varied more: Terra had no recorded violations with ungated tools,
          while a Sol run finished all its deliveries after breaking a handling rule.</p>
        <p>These observations concern the implemented system. PC2’s formal guarantee concerns the rules
          encoded in its contract and relies on authentic observations, a correct checker and execution that
          matches the formal model. A set of runs with no violations does not by itself establish those assumptions.</p>
      </div>
      <ResultFigure family="procurement" metric="safety" description="Procurement violation rates: 100% with ungated tools and 0% with PC2 for each model. Ten runs per model and condition." />
      <ResultFigure family="logistics" metric="safety" description="Logistics violation rates with ungated tools: Luna 100%, Terra 0%, Sol 10%, Astra 10%. PC2: 0% for every model. Ten runs per model and condition." />
    </section>

    <section className="v2-section shell experiment-section" id="completion" aria-labelledby="completion-title">
      <div className="reading-column">
        <p className="eyebrow">What we observed · Completion</p>
        <h2 id="completion-title">Completion depended on the model and the task</h2>
        <p>The purchasing task showed that agents could finish under the proof requirement: with PC2,
          {` ${100 * procurement.completed / procurement.runs}%`} of assignments were completed safely, compared
          with none using ungated tools. Cargo delivery was less consistent: Terra completed more assignments
          with ungated tools than with PC2, while Luna finished none in either condition.</p>
        <p>The absence of violations did not always mean the agent had done useful work: {100 * (logistics.runs - logistics.started) / logistics.runs}%
          of PC2 cargo runs never had a plan accepted. A service interruption also affected Luna’s purchasing
          results.</p>
      </div>
      <ResultFigure family="procurement" metric="completion" description="Procurement completion rates with ungated tools: 0% for every model. PC2: Luna 40%, Terra 100%, Sol 100%, Astra 100%. Ten runs per model and condition." />
      <ResultFigure family="logistics" metric="completion" description="Logistics completion rates with ungated tools: Luna 0%, Terra 100%, Sol 100%, Astra 90%. PC2: Luna 0%, Terra 80%, Sol 90%, Astra 90%. Completion is measured independently of safety. Ten runs per model and condition." />
    </section>

    <section className="v2-section shell experiment-section" id="costs" aria-labelledby="costs-title">
      <div className="reading-column">
        <p className="eyebrow">What we observed · API costs</p>
        <h2 id="costs-title">API cost rose for purchasing but sometimes fell for cargo delivery</h2>
        <p>Median API cost was higher with PC2 for every model on the purchasing assignment. For cargo delivery,
          it was higher for Luna and Terra, but lower for Sol and Astra. Low cost needs to be read alongside
          completion: Luna completed no cargo assignments in either condition.</p>
        <p>We calculated costs from recorded token usage at standard API rates dated 7 November 2026. These
          dollar figures exclude local execution and the hardware used for proof checking. They are not
          account invoice totals. Both charts include incomplete runs.</p>
      </div>
      <ResultFigure family="procurement" metric="api-cost" description="Median procurement API cost in USD. Ungated and PC2 respectively: Luna 0.04 and 0.09; Terra 0.15 and 0.25; Sol 0.91 and 1.23; Astra 5.57 and 6.50." />
      <ResultFigure family="logistics" metric="api-cost" description="Median logistics API cost in USD. Ungated and PC2 respectively: Luna 0.01 and 0.02; Terra 0.10 and 0.15; Sol 1.10 and 0.97; Astra 4.56 and 4.22." />
      <div className="reading-column" id="logistics-cost-explanation">
        <h3>The lower costs persisted on safely completed deliveries</h3>
        <p>The lower costs for Sol and Astra were not explained by cheap unsuccessful attempts. Removing
          incomplete PC2 runs lowered the median costs further.</p>
        <p>The difference also persisted when we compared each model only on scenarios it completed safely
          both with and without PC2. For both models, the median number of requests to the model was about
          13% lower with PC2, and the median number of output tokens fell too.</p>
        <p>The protected controller may help explain this reduction: once a plan was accepted, it could
          continue the work without further code from the agent for those operations. This comparison
          includes that controller and the supplied proof software, so it does not isolate the effect of
          proof checking on cost.</p>
      </div>
      <div className="reading-column experiment-reading-note" id="methods">
        <p>These tasks were chosen to reproduce specific failures found in earlier experiments. With one run
          per model, scenario and condition, the results describe this set of tasks. They do not establish
          failure rates in ordinary purchasing or delivery work. Execution settings also differed between model groups,
          limiting comparisons of model capability.</p>
      </div>
      <SiteLink className="text-link experiment-back-link" href="/overview#research">Read about the research programme <Arrow /></SiteLink>
    </section>
  </main><SiteFooter /></>;
}
