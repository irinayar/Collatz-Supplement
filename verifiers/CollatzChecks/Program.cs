using System;
// Dispatcher for the numerical checks that accompany the manuscript supplement (exhaustive scans of the first-return band).
// Usage: dotnet run -c Release -- <check> <arguments>
class Program {
  static int Main(string[] args) {
    if (args.Length == 0) { Console.WriteLine(Usage()); return 1; }
    var rest = new string[args.Length - 1]; Array.Copy(args, 1, rest, 0, rest.Length);
    switch (args[0]) {
      case "qgscan": QgScan.Run(rest); break;            // qgscan N            : all odd thresholds n<=N, total phase Q_g of genuine returns
      case "qgrecords": QgRecords.Run(rest); break;      // qgrecords N         : largest Q_g by return length and top records
      case "tail": PhaseTail.Run(rest); break;           // tail n1 n2 ...      : tail counts #(Q_g>T) at single thresholds
      case "allsource": AllSource.Run(rest); break;      // allsource n1 ...    : all-source positive charge sum (rho-1)_+
      case "runs174": Runs174.Run(rest); break;          // runs174 n1 ...      : run map and a*psi <= [2-3(2/3)^s]_+ on all runs
      case "runs176": Runs176.Run(rest); break;          // runs176 n1 ...      : expanding runs psi<=6f, b/a>=9/8; single-input runs
      case "toll": Toll.Run(rest); break;                // toll n1 ...         : telescoped K176 toll bound vs raw budget J_p
      case "census": Census.Run(rest); break;            // census range N | census single n...  : J_p, run counts, Q_g
      case "relaxedcore": RelaxedCore.Run(rest); break;  // relaxedcore n QMIN  : relaxed central core of high-phase returns
      case "lastexp": LastExp.Run(rest); break;          // lastexp n1 ...      : last exponent / arrival residue census
      case "collision": Collision.Run(rest); break;      // collision n1 ...    : same-depth same-anchor collision cells
      case "stopdp": StopDp.Run(rest); break;            // stopdp t1 t2 ...    : stopping-code weights S_t and word counts at n=3*2^70+3
      case "k180tree": K180Tree.Run(rest); break;        // k180tree N          : the six-letter residue tree of the balanced four-block words to depth N (N=8: 1,679,616 leaves)
      case "k181": K181Checks.Run(rest); break;          // k181 n1 ...        : packet identities (telescoping, kappa W_U identity) and criteria (14),(15) on all runs
      default: Console.WriteLine(Usage()); return 1;
    }
    return 0;
  }
  static string Usage() => "checks: qgscan N | qgrecords N | tail n.. | allsource n.. | runs174 n.. | runs176 n.. | toll n.. | census range N / single n.. | relaxedcore n QMIN | lastexp n.. | collision n.. | stopdp t.. | k180tree N | k181 n..";
}
