package main

import (
	"fmt"
	"os"
	"slices"
	"strconv"
	"strings"
	"time"
)

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, format+"\n", args...)
	os.Exit(1)
}

func assert(condition bool, msg string) {
	if !condition {
		fatal("Assertion failed: %s", msg)
	}
}

// negative for negation
type Literal int

func (lit Literal) neg() Literal {
	return -lit
}

func abs(lit Literal) int {
	if lit >= 0 {
		return int(lit)
	}
	return -int(lit)
}

func varIndex(p Literal) int {
	return abs(p) - 1
}

func (lit Literal) index() int {
	if lit >= 0 {
		return 2 * varIndex(lit)
	}
	return 2*varIndex(lit) + 1
}

type Assign uint8

const (
	AssignFalse Assign = iota
	AssignTrue
	AssignBottom
)

func (assign Assign) neg() Assign {
	switch assign {
	case AssignFalse:
		return AssignTrue
	case AssignTrue:
		return AssignFalse
	default:
		return AssignBottom
	}
}

type Clause struct {
	learned  bool
	activity float64
	lits     []Literal
}

type Queue struct {
	items []Literal
}

func NewQueue() *Queue {
	return &Queue{
		items: make([]Literal, 0),
	}
}

func (q *Queue) empty() bool {
	return len(q.items) == 0
}

func (q *Queue) enqueue(p Literal) {
	q.items = append(q.items, p)
}

func (q *Queue) dequeue() Literal {
	p := q.items[0]
	q.items = q.items[1:]
	return p
}

func (q *Queue) clear() {
	q.items = q.items[:0]
}

type Stats struct {
	decisions    int
	conflicts    int
	restarts     int
	creationTime time.Time
}

func newStats() *Stats {
	return &Stats{
		decisions:    0,
		conflicts:    0,
		restarts:     0,
		creationTime: time.Now(),
	}
}

type Solver struct {
	constrs               []*Clause
	learned               []*Clause
	claInc                float64
	claDecay              float64
	varInc                float64
	varDecay              float64
	activity              []float64
	watches               []([]*Clause)
	undos                 []([]*Clause)
	propQ                 *Queue
	assigns               []Assign
	shadowAssigns         []Assign
	trail                 []Literal
	trailLim              []int
	reason                []*Clause
	level                 []int
	rootLevel             int
	conflictsUntilRestart int
	restartFreq           int
	stats                 *Stats
}

func NewSolver(clauses *[][]Literal, nVars int) *Solver {
	const restartFreq = 1024
	sv := &Solver{
		constrs:               make([]*Clause, 0),
		learned:               make([]*Clause, 0),
		claInc:                1,
		claDecay:              1,
		varInc:                1.0,
		varDecay:              0.95,
		activity:              make([]float64, 0),
		watches:               make([]([]*Clause), 0),
		undos:                 make([]([]*Clause), 0),
		propQ:                 NewQueue(),
		assigns:               make([]Assign, 0),
		shadowAssigns:         make([]Assign, 0),
		trail:                 make([]Literal, 0),
		trailLim:              make([]int, 0),
		reason:                make([]*Clause, 0),
		level:                 make([]int, 0),
		rootLevel:             0,
		conflictsUntilRestart: restartFreq,
		restartFreq:           restartFreq,
		stats:                 newStats(),
	}
	for range nVars {
		sv.newVar()
	}
	for _, cl := range *clauses {
		cl, ok := sv.newClause(&cl, false)
		if !ok {
			return nil
		}
		if cl != nil {
			sv.constrs = append(sv.constrs, cl)
		}
	}
	return sv
}

func (sv *Solver) nAssigns() int {
	return len(sv.trail)
}

func (sv *Solver) nVars() int {
	return len(sv.assigns)
}

func (sv *Solver) newVar() int {
	index := sv.nVars()
	sv.watches = append(sv.watches, make([]*Clause, 0))
	sv.watches = append(sv.watches, make([]*Clause, 0))
	sv.undos = append(sv.undos, make([]*Clause, 0))
	sv.reason = append(sv.reason, nil)
	sv.assigns = append(sv.assigns, AssignBottom)
	sv.shadowAssigns = append(sv.shadowAssigns, AssignBottom)
	sv.level = append(sv.level, -1)
	sv.activity = append(sv.activity, 0)
	return index
}

func (sv *Solver) value(lit Literal) Assign {
	assign := sv.assigns[varIndex(lit)]
	if lit >= 0 {
		return assign
	}
	return assign.neg()
}

func (cl *Clause) simplify(sv *Solver) bool {
	lits := make([]Literal, 0)
	for _, p := range cl.lits {
		switch sv.value(p) {
		case AssignTrue:
			return true
		case AssignFalse:
			continue
		default:
			lits = append(lits, p)
		}
	}
	cl.lits = lits
	return false
}

func (sv *Solver) simplify() {
	constrs := make([]*Clause, 0)
	for _, cl := range sv.constrs {
		if !cl.simplify(sv) {
			constrs = append(constrs, cl)
		}
	}
	sv.constrs = constrs
}

func (sv *Solver) decisionLevel() int {
	return len(sv.trailLim)
}

func (sv *Solver) litDecisionLevel(p Literal) int {
	return sv.level[varIndex(p)]
}

func (sv *Solver) enqueue(p Literal, cl *Clause) bool {
	switch sv.value(p) {
	case AssignTrue:
		return true
	case AssignFalse:
		return false
	}
	if p > 0 {
		sv.assigns[varIndex(p)] = AssignTrue
		sv.shadowAssigns[varIndex(p)] = AssignTrue
	} else {
		sv.assigns[varIndex(p)] = AssignFalse
		sv.shadowAssigns[varIndex(p)] = AssignFalse
	}
	sv.level[varIndex(p)] = sv.decisionLevel()
	sv.reason[varIndex(p)] = cl
	sv.trail = append(sv.trail, p)
	sv.propQ.enqueue(p)
	return true
}

func (sv *Solver) clauseInWatchlist(cl *Clause) bool {
	f := func(cl2 *Clause) bool {
		return cl == cl2
	}
	return slices.ContainsFunc(sv.watches[cl.lits[0].neg().index()], f) &&
		slices.ContainsFunc(sv.watches[cl.lits[1].neg().index()], f)
}

func (cl *Clause) propagate(sv *Solver, p Literal) bool {
	assert(cl.lits[0] == p.neg() || cl.lits[1] == p.neg(), "propagate invariant")
	if cl.lits[0] == p.neg() {
		cl.lits[0] = cl.lits[1]
		cl.lits[1] = p.neg()
	}
	switch sv.value(cl.lits[0]) {
	case AssignTrue:
		sv.watches[p.index()] = append(sv.watches[p.index()], cl)
		assert(sv.clauseInWatchlist(cl), "clause in watchlist lit0 true")
		return true
	}
	for i := 2; i < len(cl.lits); i++ {
		if sv.value(cl.lits[i]) == AssignFalse {
			continue
		}
		cl.lits[1] = cl.lits[i]
		cl.lits[i] = p.neg()
		sv.watches[cl.lits[1].neg().index()] = append(sv.watches[cl.lits[1].neg().index()], cl)
		assert(sv.clauseInWatchlist(cl), "clause in watchlist found lit")
		return true
	}
	sv.watches[p.index()] = append(sv.watches[p.index()], cl)
	assert(sv.clauseInWatchlist(cl), "clause in watchlist fallback")
	cl.activity += 1
	return sv.enqueue(cl.lits[0], cl)
}

func (sv *Solver) propagate() *Clause {
	for !sv.propQ.empty() {
		p := sv.propQ.dequeue()
		tmp := make([](*Clause), len(sv.watches[p.index()]))
		copy(tmp, sv.watches[p.index()])
		sv.watches[p.index()] = []*Clause{}
		for i, cl := range tmp {
			if !cl.propagate(sv, p) {
				sv.watches[p.index()] = append(sv.watches[p.index()], tmp[i+1:]...)
				sv.propQ.clear()
				assert(sv.clauseInWatchlist(cl), "clause in watchlist conflict")
				return cl
			} else {
				assert(sv.clauseInWatchlist(cl), "clause in watchlist no-conflict")
			}
		}
	}
	return nil
}

func (sv *Solver) analyze(confl *Clause) (*[]Literal, int) {
	seen := make(map[int]bool)
	counter := 0
	p := Literal(0)
	p_reason := make([]Literal, 0)
	out_learnt := []Literal{0}
	out_btlevel := 0
	assert(sv.decisionLevel() > 0, "analyze at non-root level")
	for {
		assert(confl != nil, "analyze invariant")
		if sv.decisionLevel() == 0 {
			fmt.Println("UNSAT")
			return nil, 0
		}
		p_reason = p_reason[:0]
		confl.calcReason(p, &p_reason)
		for _, q := range p_reason {
			if seen[varIndex(q)] {
				continue
			}
			seen[varIndex(q)] = true
			if sv.litDecisionLevel(q) == sv.decisionLevel() {
				counter++
			} else if sv.litDecisionLevel(q) > 0 {
				out_learnt = append(out_learnt, q.neg())
				out_btlevel = max(out_btlevel, sv.litDecisionLevel(q))
			}
		}
		for {
			p = sv.trail[len(sv.trail)-1]
			confl = sv.reason[varIndex(p)]
			sv.undoOne()
			if seen[varIndex(p)] {
				break
			}
		}
		counter--
		if counter <= 0 {
			break
		}
	}
	out_learnt[0] = p.neg()
	return &out_learnt, out_btlevel
}

func (sv *Solver) record(lits *[]Literal, doEnqueue bool) {
	cl, ok := sv.newClause(lits, true)
	assert(ok, "record clause")
	if cl != nil {
		sv.learned = append(sv.learned, cl)
	}
	if doEnqueue {
		sv.enqueue((*lits)[0], cl)
	}
}

func (sv *Solver) undoOne() {
	p := sv.trail[len(sv.trail)-1]
	x := varIndex(p)
	sv.assigns[x] = AssignBottom
	sv.reason[x] = nil
	sv.level[x] = -1
	sv.trail = sv.trail[:len(sv.trail)-1]
}

func (sv *Solver) cancel() {
	for len(sv.trail) > sv.trailLim[len(sv.trailLim)-1] {
		sv.undoOne()
	}
	sv.trailLim = sv.trailLim[:len(sv.trailLim)-1]
}

func (sv *Solver) cancelUntil(level int) {
	for sv.decisionLevel() > level {
		sv.cancel()
	}
}

func (cl *Clause) calcReason(p Literal, out_reason *[]Literal) {
	assert(p == 0 || p == cl.lits[0], "clause calcReason invariant")
	assert(out_reason != nil, "calcReason non-nil out_reason")
	i0 := 0
	if p != 0 {
		i0 = 1
	}
	for i := i0; i < len(cl.lits); i++ {
		*out_reason = append(*out_reason, cl.lits[i].neg())
	}
}

func (sv *Solver) varRescaleActivity() {
	for i := range sv.activity {
		sv.activity[i] *= 1e-100
	}
	sv.varInc *= 1e-100
}

func (sv *Solver) varBumpActivity(p Literal) {
	v := varIndex(p)
	sv.activity[v] += sv.varInc
	if sv.varInc > 1e100 {
		sv.varRescaleActivity()
	}
}

func (sv *Solver) varDecayActivity() {
	sv.varInc *= (1 / sv.varDecay)
}

func (sv *Solver) newClause(lits *[]Literal, learned bool) (*Clause, bool) {
	var newLits []Literal
	if !learned {
		allVars := make(map[int]Literal)
		for _, p := range *lits {
			switch sv.value(p) {
			case AssignTrue:
				return nil, true
			}
			p1, found := allVars[varIndex(p)]
			if found {
				if p != p1 {
					// both a literal and its negation
					return nil, true
				}
			} else {
				// dedup on the go
				newLits = append(newLits, p)
			}
		}
	} else {
		newLits = *lits
	}
	if len(*lits) == 0 {
		return nil, false
	}
	if len(*lits) == 1 {
		return nil, sv.enqueue((*lits)[0], nil)
	}
	cl := &Clause{learned: learned, activity: 0, lits: newLits}
	if learned {
		maxDecisionLevel := 0
		maxDecisionLevelLitIndex := 0
		for i, p := range cl.lits {
			dl := sv.litDecisionLevel(p)
			if dl > maxDecisionLevel {
				maxDecisionLevel = dl
				maxDecisionLevelLitIndex = i
			}
			sv.varBumpActivity(p)
		}
		maxDecisionLevelLit := cl.lits[maxDecisionLevelLitIndex]
		cl.lits[maxDecisionLevelLitIndex] = cl.lits[1]
		cl.lits[1] = maxDecisionLevelLit
		sv.learned = append(sv.learned, cl)
	}
	sv.watches[cl.lits[0].neg().index()] = append(sv.watches[cl.lits[0].neg().index()], cl)
	sv.watches[cl.lits[1].neg().index()] = append(sv.watches[cl.lits[1].neg().index()], cl)
	assert(sv.clauseInWatchlist(cl), "clause in watchlist new clause")
	return cl, true
}

func (sv *Solver) decide() Literal {
	maxActivity := float64(-1)
	bestVar := -1

	// Find unassigned variable with highest activity
	for i, assign := range sv.assigns {
		if assign == AssignBottom && sv.activity[i] > maxActivity {
			maxActivity = sv.activity[i]
			bestVar = i
		}
	}

	if bestVar == -1 {
		return 0 // No more decisions possible
	}

	sv.stats.decisions++

	switch sv.shadowAssigns[bestVar] {
	case AssignTrue:
		return Literal(-(bestVar + 1))
	default:
		return Literal(bestVar + 1)
	}
}

func (sv *Solver) assume(p Literal) bool {
	sv.trailLim = append(sv.trailLim, len(sv.trail))
	return sv.enqueue(p, nil)
}

func (sv *Solver) checkTrailConsistency() {
	for i, lit := range sv.trail {
		if sv.value(lit) != AssignTrue {
			fmt.Fprintf(os.Stderr, "Trail inconsistency at position %d: lit %v has value %v\n",
				i, lit, sv.value(lit))
		}
	}
}

// Update search() to track statistics and print them
func (sv *Solver) search() bool {
	const statPrintFreq = 10000
	const decayFreq = 100 // Decay activities every 100 conflicts

	for {
		confl := sv.propagate()
		if confl != nil {
			sv.stats.conflicts++
			if sv.stats.conflicts%statPrintFreq == 0 {
				sv.printStats()
			}
			if sv.stats.conflicts%decayFreq == 0 {
				sv.varDecayActivity()
			}
			if sv.decisionLevel() == 0 {
				return false
			}
			learnt, backtrackLevel := sv.analyze(confl)
			sv.conflictsUntilRestart--
			if sv.conflictsUntilRestart == 0 {
				sv.stats.restarts++
				sv.restartFreq = 2 * sv.restartFreq
				sv.conflictsUntilRestart = sv.restartFreq
				sv.cancelUntil(0)
				sv.record(learnt, false)
			} else {
				sv.cancelUntil(max(backtrackLevel, sv.rootLevel))
				sv.record(learnt, true)
			}
		} else {
			if sv.nAssigns() == sv.nVars() {
				return true
			} else {
				decision := sv.decide()
				sv.assume(decision)
			}
		}
	}
}

// Add method to print statistics
func (sv *Solver) printStats() {
	uptime := time.Since(sv.stats.creationTime).Seconds()
	fmt.Printf("c %.2fs decisions %d conflicts %d restarts %d\n", uptime, sv.stats.decisions, sv.stats.conflicts, sv.stats.restarts)
}

func parseDimacs(filename string) (*[][]Literal, int) {
	nVars := 0
	nClauses := 0
	data, err := os.ReadFile(filename)
	if err != nil {
		fatal("Error reading file: %v", err)
	}
	clauses := make([][]Literal, 0)
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		if line == "" || line[0] == 'c' {
			continue
		}
		if line[0] == 'p' {
			fields := strings.Fields(line)
			if len(fields) >= 4 {
				nVars, err = strconv.Atoi(fields[2])
				if err != nil {
					fatal("Invalid vars number in DIMACS file")
				}
				nClauses, err = strconv.Atoi(fields[3])
				if err != nil {
					fatal("Invalid clauses number in DIMACS file")
				}
			} else {
				fatal("Invalid DIMACS file")
			}
			continue
		}
		lits0 := strings.Fields(line)
		lits := make([]Literal, 0)
		for _, lit := range lits0 {
			if lit == "" || lit == "0" {
				continue
			}
			num, err := strconv.Atoi(lit)
			if err != nil {
				fatal("Invalid literal in DIMACS file: %s", lit)
			}
			lits = append(lits, Literal(num))
		}
		slices.Sort(lits)
		clauses = append(clauses, slices.Compact(lits))
	}
	if nClauses != len(clauses) {
		fmt.Printf("c invalid DIMACS file: %d clauses claimed, %d clauses in file", nClauses, len(clauses))
	}
	return &clauses, nVars
}

func (sv *Solver) check(clauses *[]*Clause) *Clause {
	for _, cl := range *clauses {
		hasSatisfied := slices.ContainsFunc(cl.lits, func(p Literal) bool {
			return sv.value(p) == AssignTrue
		})
		if !hasSatisfied {
			return cl
		}
	}
	return nil
}

func (sv *Solver) printModel() {
	const lineLimit = 20
	fmt.Println("s SATISFIABLE")
	for i, assign := range sv.assigns {
		if i == 0 {
			fmt.Print("v ")
		} else if i%lineLimit == 0 {
			fmt.Print("\nv ")
		}
		if assign == AssignTrue {
			fmt.Print(i + 1)
		} else if assign == AssignFalse {
			fmt.Print(-(i + 1))
		} else {
			assert(false, "invalid assignment")
		}
		if i%lineLimit < lineLimit-1 && i != len(sv.assigns)-1 {
			fmt.Print(" ")
		}
	}
	fmt.Println("\nv 0")
}

func printUnsat() {
	fmt.Println("s UNSATISFIABLE")
	os.Exit(0)
}

func main() {
	if len(os.Args) != 2 {
		fmt.Println("Usage: satie <dimacs_file>")
		os.Exit(1)
	}
	clauses, nVars := parseDimacs(os.Args[1])
	sv := NewSolver(clauses, nVars)
	if sv == nil {
		printUnsat()
	}
	if sv.search() {
		cl := sv.check(&sv.constrs)
		if cl == nil {
			cl = sv.check(&sv.learned)
		}
		if cl != nil {
			sv.checkTrailConsistency()
			fatal("clause is not satisfied: %v", cl)
		}
		sv.printStats()
		sv.printModel()
		sv.cancelUntil(0)
	} else {
		sv.printStats()
		printUnsat()
	}
}
