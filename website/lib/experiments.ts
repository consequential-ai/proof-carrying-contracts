import measurements from './operational-results.json';

export type ExperimentFamily = 'procurement' | 'logistics';
export const experimentGroups = measurements.groups;
export const logisticsCostAnalysis = measurements.logisticsCostAnalysis;
export const experimentAssets = '/experiments/operational-002';

export function experimentSummary(family: ExperimentFamily, arm: 'ungated' | 'pc2') {
  return experimentGroups.filter(row => row.family === family && row.arm === arm)
    .reduce((total, row) => ({
      runs: total.runs + row.runs,
      violations: total.violations + row.violations,
      completed: total.completed + row.safeCompleted,
      started: total.started + row.runs - row.notStarted,
    }), { runs: 0, violations: 0, completed: 0, started: 0 });
}

export const formatMeasure = (value: number) => new Intl.NumberFormat('en-GB', {
  maximumFractionDigits: 1,
}).format(value);
