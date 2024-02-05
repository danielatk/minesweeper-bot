"use strict";

const BOMB = 9;
const ACTION_CLEAR = 1;
const ACTION_FLAG = 2;
const ACTION_CHORD = 3;

const PLAY_STYLE_EFFICIENCY = 3;
const PLAY_STYLE_NOFLAGS_EFFICIENCY = 4;

const power10n = [BigInt(1), BigInt(10), BigInt(100), BigInt(1000), BigInt(10000), BigInt(100000), BigInt(1000000)];
const power10 = [1, 10, 100, 1000, 10000, 100000, 1000000];
const maxSolutionsDisplay = BigInt("100000000000000000");

const OFFSETS = [[2, 0], [-2, 0], [0, 2], [0, -2]];
const OFFSETS_ALL = [[2, -2], [2, -1], [2, 0], [2, 1], [2, 2], [-2, -2], [-2, -1], [-2, 0], [-2, 1], [-2, 2], [-1, 2], [0, 2], [1, 2], [-1, -2], [0, -2], [1, -2]];

const PLAY_BFDA_THRESHOLD = 1000;       // number of solutions for the Brute force analysis to start
const BRUTE_FORCE_CYCLES_THRESHOLD = 1000000;
const HARD_CUT_OFF = 0.90;        // cutoff for considering on edge possibilities below the best probability
const OFF_EDGE_THRESHOLD = 0.95;  // when to include possibilities off the edge
const PROGRESS_CONTRIBUTION = 0.2;  // how much progress counts towards the final score

const USE_HIGH_DENSITY_STRATEGY = false;  // I think "secondary safety" generally works better than "solution space reduction"

const PLAY_STYLE_FLAGS = 1;

let canvasLocked = false;
let analysing = false;

let BINOMIAL;

let board;

const HIDDEN = 10;
const FLAGGED = 11;
const FLAGGED_WRONG = 12;
const EXPLODED = 13;

const PLAY_STYLE_NOFLAGS = 2;

let showHints = true;
let playStyle = 'flag';
let overlay = 'none';

let justPressedAnalyse = false;

class PrimeSieve {


	constructor(n) {

		if (n < 2) {
			this.max = 2;
		} else {
			this.max = n;
		}

		this.composite = Array(this.max).fill(false);

		const rootN = Math.floor(Math.sqrt(n));

		for (let i = 2; i < rootN; i++) {

			// if this is a prime number (not composite) then sieve the array
			if (!this.composite[i]) {
				let index = i + i;
				while (index <= this.max) {
					this.composite[index] = true;
					index = index + i;
				}
			}
		}

	}
	
	isPrime(n) {
		if (n <= 1 || n > this.max) {
			throw new Error("Prime check is outside of range: " + n);
		}

		return !this.composite[n];
	}
 	
}

class Binomial {

	constructor(max, lookup) {

		this.max = max;

		this.ps = new PrimeSieve(this.max);

		if (lookup < 10) {
			lookup = 10;
		}
		this.lookupLimit = lookup;

		const lookup2 = lookup / 2;

		this.binomialLookup = Array(lookup + 1);

		for (let total = 1; total <= lookup; total++) {

			this.binomialLookup[total] = Array(lookup2 + 1);

			for (let choose = 0; choose <= total / 2; choose++) {
				this.binomialLookup[total][choose] = this.generate(choose, total);
			}


		}

	}


	generate(k, n) {

		if (n == 0 && k == 0) {
			return BigInt(1);
		}

		if (n < 1 || n > this.max) {
			throw new Error("Binomial: 1 <= n and n <= max required, but n was " + n + " and max was " + this.max);
		}

		if (0 > k || k > n) {
			console.log("Binomial: 0 <= k and k <= n required, but n was " + n + " and k was " + k);
			throw new Error("Binomial: 0 <= k and k <= n required, but n was " + n + " and k was " + k);
		}

		var choose = Math.min(k, n - k);

		var answer;
		if (n <= this.lookupLimit) {
			answer = this.binomialLookup[n][choose];
		}

		if (answer != null) {
			return answer;
		} else if (choose < 25) {
			return this.combination(choose, n);
		} else {
			return this.combinationLarge(choose, n);
		}

	}
	
    combination(mines, squares) {

		let top = BigInt(1);
		let bot = BigInt(1);

		const range = Math.min(mines, squares - mines);

		// calculate the combination. 
		for (let i = 0; i < range; i++) {
			top = top * BigInt(squares - i);
			bot = bot* BigInt(i + 1);
		}

		const result = top / bot;

		return result;

	}    
	
	
	combinationLarge(k, n) {

		if ((k == 0) || (k == n)) return BigInt(1);

		const n2 = n / 2;

		if (k > n2) {
			k = n - k;
		}

		const nk = n - k;

		const rootN = Math.floor(Math.sqrt(n));

		let result = BigInt(1);

		for (let prime = 2; prime <= n; prime++) {

			// we only want the primes
			if (!this.ps.isPrime(prime)) {
				continue;
            }

			if (prime > nk) {
				result = result * BigInt(prime);
				continue;
			}

			if (prime > n2) {
				continue;
			}

			if (prime > rootN) {
				if (n % prime < k % prime) {
					result = result * BigInt(prime);
				}
				continue;
			}

			let r = 0;
			let N = n;
			let K = k;
			let p = 1;

			let safety = 100;
			while (N > 0) {
				r = (N % prime) < (K % prime + r) ? 1 : 0;
				if (r == 1) {
					p *= prime;
				}
				N = Math.floor( N / prime);
				K = Math.floor( K / prime);
				//console.log("r=" + r + " N=" + N + " k=" + k + " p=" + p);
				safety--;
				if (safety < 1) {
					console.log("Safety stop!!!");
					break;
                }
			}
			if (p > 1) {
				result = result * BigInt(p);
			}
		}

		return result;
	}

}

class Action {
    constructor(x, y, prob, action) {
        this.x = x;
        this.y = y;
        this.prob = prob;
        this.action = action;
        this.dead = false;
        this.pruned = false;

        // part of full analysis output, until then assume worst case 
        this.progress = 0;
        this.expectedClears;
        this.weight = prob;
        this.maxSolutions;
        this.commonClears;
    }

    asText() {

        return "(" + this.x + "," + this.y + "): " + this.action.action;

    }

}

class Tile {
	constructor(x, y, index) {
		this.x = x;
		this.y = y;
		this.is_covered = true;
		this.value = 0;
		this.is_flagged = false;
		this.foundBomb = false
        this.is_bomb = null;   // this gets set when the game is lost
        this.exploded = false;  // this gets set if this tile was the one clicked
        this.index = index;

        this.onEdge = false;
        this.hint = false;
        this.probability = -1;  // of being safe
		this.hintText = "";
		this.hasHint = false;

		this.efficiencyValue = "";   // the value we need to be to be chordable
		this.efficiencyProbability = 0;  // the probability of being that value
		this.efficiencyText = "";  

		// is there a mine adjacent to this tile?  Set as part of the No flag efficiency logic
		this.adjacentMine = false;

		Object.seal(this); // prevent new values being created
	}

	getX() {
		return this.x;
	}
	
	getY() {
		return this.y;
	}
	
	// returns true if the tile provided is adjacent to this tile
	isAdjacent(tile) {
		
		const dx = Math.abs(this.x - tile.x);
		const dy = Math.abs(this.y - tile.y);
		
		// adjacent and not equal
		if (dx < 2 && dy < 2 && !(dx == 0 && dy == 0)) {
			return true;
		} else {
			return false;
		}
		
	}

    isEqual(tile) {

        if (this.x == tile.x && this.y == tile.y) {
            return true;
        } else {
            return false;
        }

    }

	asText() {
		return "(" + this.x + "," + this.y + ")";
	}

    getHintText() {

        if (!this.hasHint) {
            return "";
		} else {
			return this.hintText + this.efficiencyText;
        }

    }

	getHasHint() {
		return this.hasHint;
    }

    setProbability(prob, progress, safety2) {
        this.probability = prob;
        this.hasHint = true;

		if (prob == 1) {
			this.hintText = "Clear";
		} else if (prob == 0) {
			this.hintText = "Mine";
		} else if (progress == null) {
			this.hintText = "\n" + (prob * 100).toFixed(2) + "% safe";
		} else {
			this.hintText = "\n" + (prob * 100).toFixed(2) + "% safe" + "\n" + (safety2 * 100).toFixed(2) + "% 2nd safety" + "\n" + (progress * 100).toFixed(2) + "% progress"
        }

	}

	setValueProbability(value, probability) {
		this.efficiencyValue = value;
		this.efficiencyProbability = probability;

		this.efficiencyText = "\n" + (probability * 100).toFixed(2) + "% value '" + value + "'"
	}

    //getProbability() {
    //    return this.probability;
    //}

    clearHint() {
        this.onEdge = false;
        this.hasHint = false;
		this.hintText = "";
		this.efficiencyValue = null;
		this.efficiencyProbability = 0;
		this.efficiencyText = "";
		this.probability = -1;
    }

    setOnEdge() {
        this.onEdge = true;
    }

	isCovered() {
		return this.is_covered;
	}

	setCovered(covered) {
		this.is_covered = covered;
    }

	setValue(value) {
		this.value = value;
		this.is_covered = false;
	}

	setValueOnly(value) {
		this.value = value;
    }

	getValue() {
		return this.value;
	}

	rotateValue(delta) {

		var newValue = this.value + delta;

		if (newValue < 0) {
			newValue = 8;
		} else if (newValue > 8) {
			newValue = 0;
        }

		this.setValue(newValue);
    }

	toggleFlag() {
		this.is_flagged = !this.is_flagged;
	}
	
	isFlagged() {
		return this.is_flagged;
	}

	// this is set when the solver discovers a bomb - trying to separate the discovery of a bomb from the flagging of a tile
	setFoundBomb() {
		//console.log(this.asText() + " set to Found Bomb");
		this.foundBomb = true;
	}

	// this is used when a tile is speculatively set to a mine to see if the board is still valid
	unsetFoundBomb() {
		//console.log(this.asText() + " set to not Found Bomb");
		this.foundBomb = false;
	}

	isSolverFoundBomb() {
		return this.foundBomb;
    }

	// this is used to display the bombs when the game is lost
	setBomb(bomb) {
		this.is_bomb = bomb;
	}

	// this is used to display the exploded bomb when the game is lost
    setBombExploded() {
        this.is_bomb = true;
        this.exploded = true;
    }

	isBomb() {
		return this.is_bomb;
	}
}

class Board {
	
	constructor(id, width, height, num_bombs) {
		
		console.log('Creating a new board with id=' + id + ' ...');

		this.MAX = 4294967295;

        this.id = id;
		this.width = width;
		this.height = height;
        this.num_bombs = num_bombs;

		this.tiles = [];
		this.started = false;
		this.bombs_left = this.num_bombs;

		this.init_tiles();

		this.gameover = false;
		this.won = false;

		this.highDensity = false;

		console.log('... board created');

		Object.seal(this) // prevent new properties being created
	}

	isStarted() {
		return this.started;
	}
	
	setGameLost() {
		this.gameover = true;
	}

    setGameWon() {
        this.gameover = true;
        this.won = true;
    }

	isGameover() {
		return this.gameover;
	}
	
	
	getID() {
		return this.id;
	}
	
	setStarted() {
		
		if (this.start) {
			console.log('Logic error: starting the same game twice');
			return;
		}
		
		this.started = true;
	}

	setHighDensity(tilesLeft, minesLeft) {

		if (minesLeft * 5 > tilesLeft * 2) {
			this.highDensity = true;
		} else {
			this.highDensity = false;
        }

    }

	isHighDensity() {
		return this.highDensity;
    }

	xy_to_index(x, y) {
		return y*this.width + x;
	}
	
	getTileXY(x, y) {

		if (x < 0 || x >= this.width || y < 0 || y >= this.height) {
			return null;
        }

		const index = this.xy_to_index(x,y);
		
		return this.tiles[index];
		
	}
	
	getTile(index) {
		
		return this.tiles[index];
		
	}
	
	// true if number of flags == tiles value
	// and number of unrevealed > 0
	canChord(tile) {
		
		let flagCount = 0;
		let coveredCount = 0;		
		for (let adjTile of this.getAdjacent(tile)) {
			if (adjTile.isFlagged()) {  
				flagCount++;
			}
			if (adjTile.isCovered() && !adjTile.isFlagged()) {  
				coveredCount++;
			}
		}
		
		return (flagCount == tile.getValue()) && (coveredCount > 0);
		
	}

    // return number of confirmed mines adjacent to this tile
    adjacentFoundMineCount(tile) {

        let mineCount = 0;
        for (let adjTile of this.getAdjacent(tile)) {
			if (adjTile.isSolverFoundBomb()) {
                mineCount++;
            }
        }

        return mineCount;

    }

	// return number of flags adjacent to this tile
	adjacentFlagsPlaced(tile) {

		let flagCount = 0;
		for (let adjTile of this.getAdjacent(tile)) {
			if (adjTile.isFlagged()) {
				flagCount++;
			}
		}

		return flagCount;

	}

    // return number of covered tiles adjacent to this tile
    adjacentCoveredCount(tile) {

        let coveredCount = 0;
        for (let adjTile of this.getAdjacent(tile)) {
			//if (adjTile.isCovered() && !adjTile.isFlagged()) {
			if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                coveredCount++;
            }
        }

        return coveredCount;

    }

	// header for messages sent to the server
	getMessageHeader() {
        return { 'id': this.id, 'width': this.width, 'height': this.height, 'mines': this.num_bombs};
	}
	
	// returns all the tiles adjacent to this tile
	getAdjacent(tile) {
		
		const col = tile.x;
		const row = tile.y;

		const first_row = Math.max(0, row - 1);
		const last_row = Math.min(this.height - 1, row + 1);

		const first_col = Math.max(0, col - 1);
		const last_col = Math.min(this.width - 1, col + 1);

		const result = []

		for (let r = first_row; r <= last_row; r++) {
			for (let c = first_col; c <= last_col; c++) {
				if (!(r == row && c == col)) {  // don't include ourself
					const i = this.width * r + c;
					result.push(this.tiles[i]);
				}
			}
		}

		return result;
	}

	getFlagsPlaced() {

		let tally = 0;
		for (let i = 0; i < this.tiles.length; i++) {
			if (this.tiles[i].isFlagged()) {
				tally++;
            }
        }
			 
		return tally;
    }

	// sets up the initial tiles 
	init_tiles() {
		
		for (let y=0; y < this.height; y++) {
			for (let x=0; x < this.width; x++) {
				this.tiles.push(new Tile(x, y, y * this.width + x));
			}
		}
		
	}

	setAllZero() {
		for (let i = 0; i < this.tiles.length; i++) {
			this.tiles[i].setValue(0);
		}
    }

	resetForAnalysis() {

		for (let i = 0; i < this.tiles.length; i++) {
			const tile = this.tiles[i];
			if (tile.isFlagged()) {
				tile.foundBomb = true;
			} else {
				tile.foundBomb = false;
            }
		}

    }

	getHashValue() {

		let hash = (31 * 31 * 31 * this.num_bombs + 31 * 31 * this.getFlagsPlaced() + 31 * this.width + this.height) % this.MAX;

		for (let i = 0; i < this.tiles.length; i++) {
			const tile = this.tiles[i];
			if (tile.isFlagged()) {
				hash = (31 * hash + 13) % this.MAX;
			} else if (tile.isCovered()) {
				hash = (31 * hash + 12) % this.MAX;
			} else {
				hash = (31 * hash + tile.getValue()) % this.MAX;
			}
        }

		return hash;
	}

	// returns a string that represents this board state which can be save and restored later
	getStateData() {

		// wip

		for (var i = 0; i < this.tiles.length; i++) {
			var tile = this.tiles[i];
			if (tile.isFlagged()) {
				hash = (31 * hash + 13) % this.MAX;
			} else if (tile.isCovered()) {
				hash = (31 * hash + 12) % this.MAX;
			} else {
				hash = (31 * hash + tile.getValue()) % this.MAX;
			}
		}


	}

	findAutoMove() {

		const result = new Map();

		for (let i = 0; i < this.tiles.length; i++) {

			const tile = this.getTile(i);

			if (tile.isFlagged()) {
				continue;  // if the tile is a mine then nothing to consider
			} else if (tile.isCovered()) {
				continue;  // if the tile hasn't been revealed yet then nothing to consider
			}

			const adjTiles = this.getAdjacent(tile);

			let needsWork = false;
			let flagCount = 0;
			let coveredCount = 0;
			for (let j = 0; j < adjTiles.length; j++) {
				const adjTile = adjTiles[j];
				if (adjTile.isCovered() && !adjTile.isFlagged()) {
					needsWork = true;
				}
				if (adjTile.isFlagged()) {
					flagCount++;
				} else if (adjTile.isCovered()) {
					coveredCount++;
                }
			}

			if (needsWork) {  // the witness still has some unrevealed adjacent tiles
				if (tile.getValue() == flagCount) {  // can clear around here
					for (let j = 0; j < adjTiles.length; j++) {
						const adjTile = adjTiles[j];
						if (adjTile.isCovered() && !adjTile.isFlagged()) {
							result.set(adjTile.index, new Action(adjTile.getX(), adjTile.getY(), 1, ACTION_CLEAR));
						}
					}			

				} else if (tile.getValue() == flagCount + coveredCount) { // can place all flags
					for (let j = 0; j < adjTiles.length; j++) {
						const adjTile = adjTiles[j];
						if (adjTile.isCovered() && !adjTile.isFlagged()) { // if covered and isn't flagged
							adjTile.setFoundBomb();   // Must be a bomb
							result.set(adjTile.index, new Action(adjTile.getX(), adjTile.getY(), 0, ACTION_FLAG));
						}
					}			
                }
			}

		}	

		// send it back as an array
		return Array.from(result.values());

	} 

	getFormatMBF() {

		if (this.width > 255 || this.height > 255) {
			console.log('Board too large to save as MBF format');
			return null;
        }

		const length = 4 + 2 * this.num_bombs;

		const mbf = new ArrayBuffer(length);
		const mbfView = new Uint8Array(mbf);

		mbfView[0] = this.width;
		mbfView[1] = this.height;

		mbfView[2] = Math.floor(this.num_bombs / 256);
		mbfView[3] = this.num_bombs % 256;

		let minesFound = 0;
		let index = 4;
		for (let i = 0; i < this.tiles.length; i++) {

			const tile = this.getTile(i);

			if (tile.isFlagged()) {
				minesFound++;
				if (index < length) {
					mbfView[index++] = tile.getX();
					mbfView[index++] = tile.getY();
                }
			}
		}

		if (minesFound != this.num_bombs) {
			console.log('Board has incorrect number of mines. board=' + this.num_bombs + ', found=' + minesFound);
			return null;
		}

		console.log(...mbfView);

		return mbf;

    }

	getPositionData() {

		const newLine = '\n';

		let data = this.width + 'x' + this.height + 'x' + this.num_bombs + newLine;

		for (let y = 0; y < this.height; y++) {
			for (let x = 0; x < this.width; x++) {
				const tile = this.getTileXY(x, y);
				if (tile.isFlagged()) {
					data = data + 'F';

				} else if (tile.isCovered() || tile.isBomb()) {
					data = data + 'H';

				} else {
					data = data + tile.getValue();
                } 
			}
			data = data + newLine;
        }

		return data;

    }

}

// these variables are used across the family of classes used in this process
class BruteForceGlobal {

    // constants used in this processing
    static BRUTE_FORCE_ANALYSIS_MAX_NODES = 1000000;
    static PRUNE_BF_ANALYSIS = true;
    static BRUTE_FORCE_ANALYSIS_TREE_DEPTH = 4;

    static ACTION_CLEAR = 1;
    static ACTION_FLAG = 2;
    static ACTION_CHORD = 3;

    static INDENT = "................................................................................";

    // globals used in this processing
    static processCount = 0;   // how much work has been done
    static allSolutions;       // this is class 'SolutionTable'
    static allTiles;           // this is an array of the tiles being analysed 

    // cache details
    static cache = new Map();
    static cacheHit = 0;
    static cacheWinningLines = 0;

}


class BruteForceAnalysis {

	constructor(solutions, tiles, size, verbose) {  // tiles is array of class 'Tile' being considered

        BruteForceGlobal.allTiles = tiles;

        this.allDead = false;   // this is true if all the locations are dead
        this.deadTiles = [];

        this.winChance;
        this.currentNode;
        this.expectedMove;

        this.bestTile;
        this.processedMoves = [];

        //this.maxSolutionSize = size;
        this.completed = false;

        this.verbose = verbose;

        // reset the globals
        BruteForceGlobal.allSolutions = new SolutionTable(solutions);
        BruteForceGlobal.cache.clear();  //clear the cache
        BruteForceGlobal.cacheHit = 0;
        BruteForceGlobal.cacheWinningLines = 0;
        BruteForceGlobal.processCount = 0;
    }

    async process() {

        const start = performance.now();

        this.writeToConsole("----- Brute Force Deep Analysis starting ----");
        this.writeToConsole(BruteForceGlobal.allSolutions.size() + " solutions in BruteForceAnalysis");

        // create the top node 
        let top = this.buildTopNode(BruteForceGlobal.allSolutions);  // top is class 'Node'

        if (top.getLivingLocations().length == 0) {
            this.allDead = true;
        }

        let best = 0;

        for (let i = 0; i < top.getLivingLocations().length; i++) {

            if (this.verbose) {
                console.log("Analysing Brute Force Deep Analysis line " + i + " of " + top.getLivingLocations().length);
                await sleep(1);
            }
 
            const move = top.getLivingLocations()[i];  // move is class 'Livinglocation'

            const winningLines = top.getWinningLinesStart(move);  // calculate the number of winning lines if this move is played

            // if the move wasn't pruned is it a better move
            if (!move.pruned) {
                if (best < winningLines || (top.bestLiving != null && best == winningLines && top.bestLiving.mineCount < move.mineCount)) {
                    best = winningLines;
                    top.bestLiving = move;
                }
            }

            const singleProb = (BruteForceGlobal.allSolutions.size() - move.mineCount) / BruteForceGlobal.allSolutions.size();

            if (move.pruned) {
                this.writeToConsole(move.index + " " + BruteForceGlobal.allTiles[move.index].asText() + " is living with " + move.count + " possible values and probability "
                    + this.percentage(singleProb) + ", this location was pruned (max winning lines " + winningLines + ", process count " + BruteForceGlobal.processCount + ")");
            } else {
                this.writeToConsole(move.index + " " + BruteForceGlobal.allTiles[move.index].asText() + " is living with " + move.count + " possible values and probability "
                    + this.percentage(singleProb) + ", winning lines " + winningLines + " (" + "process count " + BruteForceGlobal.processCount + ")");
            }

            if (BruteForceGlobal.processCount < BruteForceGlobal.BRUTE_FORCE_ANALYSIS_MAX_NODES) {
                this.processedMoves.push(BruteForceGlobal.allTiles[move.index]);  // store the tiles we've processed
            }

        }

        top.winningLines = best;

        this.currentNode = top;

        // this is the best tile to guess (or the best we've calculated if incomplete).  "Tile" class.
        if (top.bestLiving != null) {
            this.bestTile = BruteForceGlobal.allTiles[top.bestLiving.index];
        }
 

        if (BruteForceGlobal.processCount < BruteForceGlobal.BRUTE_FORCE_ANALYSIS_MAX_NODES) {
            this.winChance = best / BruteForceGlobal.allSolutions.size() ;
            this.completed = true;
            if (true) {
                this.writeToConsole("--------- Probability Tree dump start ---------");
                this.showTree(0, 0, top);
                this.writeToConsole("---------- Probability Tree dump end ----------");
            }
        }

        const end = performance.now();;
        this.writeToConsole("Total nodes in cache = " + BruteForceGlobal.cache.size + ", total cache hits = " + BruteForceGlobal.cacheHit + ", total winning lines saved = " + BruteForceGlobal.cacheWinningLines);
        this.writeToConsole("process took " + (end - start) + " milliseconds and explored " + BruteForceGlobal.processCount + " nodes");
        this.writeToConsole("----- Brute Force Deep Analysis finished ----");

        // clear down the cache
        BruteForceGlobal.cache.clear();

    }

    // 6020245077845603
    checkForBetterMove(guess) {

        // if we haven't processed 2 tiles or this tile is the best then stick with it
        if (this.processedMoves.length < 2 || (guess.x == this.bestTile.x && guess.y == this.bestTile.y)) {
            return null;
        }

        for (let tile of this.processedMoves) {
            if (guess.x == tile.x && guess.y == tile.y) {  // if we have processed the guess and it isn't the best tile then return the best tile
                return this.bestTile;
            }
        }

        //  otherwise nothing better
        return null;

    }

	/**
	 * Builds a top of tree node based on the solutions provided
	 */
	buildTopNode(solutionTable) {

        const result = new Node();   

        result.startLocation = 0;
        result.endLocation = solutionTable.size();

        const living = [];  // living is an array of 'LivingLocation'

        for (let i = 0; i < BruteForceGlobal.allTiles.length; i++) {
            let value;

            const valueCount = new Array(9).fill(0);
            let mines = 0;
            let maxSolutions = 0;
            let count = 0;
            let minValue = 0;
            let maxValue = 0;

            for (let j = 0; j < result.getSolutionSize(); j++) {
                if (solutionTable.get(j)[i] != BOMB) {
                    value = solutionTable.get(j)[i];
                    valueCount[value]++;
                } else {
                    mines++;
                }
            }

            for (let j = 0; j < valueCount.length; j++) {
                if (valueCount[j] > 0) {
                    if (count == 0) {
                        minValue = j;
                    }
                    maxValue = j;
                    count++;
                    if (maxSolutions < valueCount[j]) {
                        maxSolutions = valueCount[j];
                    }
                }
            }
            if (count > 1) {
                const alive = new LivingLocation(i);   // alive is class 'LivingLocation'
                alive.mineCount = mines;
                alive.count = count;
                alive.minValue = minValue;
                alive.maxValue = maxValue;
                alive.maxSolutions = maxSolutions;
                alive.zeroSolutions = valueCount[0];
                living.push(alive);
            } else {
                console.log(BruteForceGlobal.allTiles[i].asText() + " is dead with value " + minValue);
                this.deadTiles.push(BruteForceGlobal.allTiles[i]);   // store the dead tiles
            }

        }

        living.sort((a, b) => a.compareTo(b));

        result.livingLocations = living;

        return result;
    }   


 
    getNextMove() {

        const bestLiving = this.getBestLocation(this.currentNode);  /// best living is 'LivingLocation'

        if (bestLiving == null) {
            return null;
        }

        const loc = BruteForceGlobal.allTiles[bestLiving.index];  // loc is class 'Tile'

        //solver.display("first best move is " + loc.display());
        const prob = 1 - (bestLiving.mineCount / this.currentNode.getSolutionSize());

        console.log("mines = " + bestLiving.mineCount + " solutions = " + this.currentNode.getSolutionSize());
        for (let i = 0; i < bestLiving.children.length; i++) {
            if (bestLiving.children[i] == null) {
                //solver.display("Value of " + i + " is not possible");
                continue; //ignore this node but continue the loop
            }

            let probText;
            if (bestLiving.children[i].bestLiving == null) {
                probText = 1 / bestLiving.children[i].getSolutionSize();
            } else {
                probText = bestLiving.children[i].getProbability();
            }
            console.log("Value of " + i + " leaves " + bestLiving.children[i].getSolutionSize() + " solutions and winning probability " + probText + " (work size " + bestLiving.children[i].work + ")");
        }

        const action = new Action(loc.getX(), loc.getY(), prob, ACTION_CLEAR);

        this.expectedMove = loc;

        return action;

    }
	
	getBestLocation(node) {
        return node.bestLiving;
    }
	
	
	showTree(depth, value, node) {

        let condition;
        if (depth == 0) {
            condition = node.getSolutionSize() + " solutions remain";
        } else {
            condition = "When '" + value + "' ==> " + node.getSolutionSize() + " solutions remain";
        }

        if (node.bestLiving == null) {
            const line = BruteForceGlobal.INDENT.substring(0, depth * 3) + condition + " Solve chance " + node.getProbability();

            this.writeToConsole(line);
            return;
        }

        const loc = BruteForceGlobal.allTiles[node.bestLiving.index];

        const prob = 1 - (node.bestLiving.mineCount / node.getSolutionSize());


        const line = BruteForceGlobal.INDENT.substring(0, depth * 3) + condition + " play " + loc.asText() + " Survival chance " + prob + ", Solve chance " + node.getProbability();
        this.writeToConsole(line);

        for (let val = 0; val < node.bestLiving.children.length; val++) {
            const nextNode = node.bestLiving.children[val];
            if (nextNode != null) {
                this.showTree(depth + 1, val, nextNode);
            }
        }

    }


    getExpectedMove() {
        return this.expectedMove;
    }
	
	percentage(prob) {
        return prob * 100;
    }

    allTilesDead() {
        return this.allDead;
    }

    writeToConsole(text) {
        if (this.verbose) {
            console.log(text);
        }
    }

}


/**
 * A key to uniquely identify a position
 */
class Position {

    constructor(p, index, value) {

        this.position;
        this.hash = 0;
        this.mod = BigInt(Number.MAX_SAFE_INTEGER);


        if (p == null) {
            this.position = new Array(BruteForceGlobal.allTiles.length).fill(15);
        } else {
            // copy and update to reflect the new position
            this.position = p.position.slice(); 
            //this.position.push(...p.position); 
            this.position[index] = value + 50;
        }

    }

 
    // copied from String hash
    hashCode() {
        let h = BigInt(this.hash);
        if (h == 0 && this.position.length > 0) {
            for (let i = 0; i < this.position.length; i++) {
                h = (BigInt(31) * h + BigInt(this.position[i])) % this.mod;
            }
            this.hash = Number(h);  // convert back to a number
        }
        return this.hash;
    }

}

/**
 * Positions on the board which can still reveal information about the game.
 */
class LivingLocation {

    constructor (index) {
        this.index = index;

        this.pruned = false;
        this.mineCount = 0;  // number of remaining solutions which have a mine in this position
        this.maxSolutions = 0;    // the maximum number of solutions that can be remaining after clicking here
        this.zeroSolutions = 0;    // the number of solutions that have a '0' value here
        this.maxValue = -1;
        this.minValue = -1;
        this.count;  // number of possible values at this location

        this.children;  // children is an array of class 'Node'

    }

    /**
     * Determine the Nodes which are created if we play this move. Up to 9 positions where this locations reveals a value [0-8].
     */
    buildChildNodes(parent) {  // parent is class 'Node'

        // sort the solutions by possible values
        BruteForceGlobal.allSolutions.sortSolutions(parent.startLocation, parent.endLocation, this.index);
        let index = parent.startLocation;

        const work = Array(9);  // work is an array of class 'Node' with size 9

        for (let i = this.minValue; i < this.maxValue + 1; i++) {

             // if the node is in the cache then use it
            const pos = new Position(parent.position, this.index, i);

            const temp1 = BruteForceGlobal.cache.get(pos.hashCode());  // temp1 is class 'Node'

            if (temp1 == null) {

                const temp = new Node(pos);

                temp.startLocation = index;
                // find all solutions for this values at this location
                while (index < parent.endLocation && BruteForceGlobal.allSolutions.get(index)[this.index] == i) {
                    index++;
                }
                temp.endLocation = index;

                work[i] = temp;

            } else {
                work[i] = temp1;
                BruteForceGlobal.cacheHit++;
                BruteForceGlobal.cacheWinningLines = BruteForceGlobal.cacheWinningLines + temp1.winningLines;
                // skip past these details in the array
                while (index < parent.endLocation && BruteForceGlobal.allSolutions.get(index)[this.index] <= i) {
                    index++;
                }
            }
        }

        // skip over the mines
        while (index < parent.endLocation && BruteForceGlobal.allSolutions.get(index)[this.index] == BOMB) {
            index++;
        }

        if (index != parent.endLocation) {
            console.log("**** Didn't read all the elements in the array; index = " + index + " end = " + parent.endLocation + " ****");
        }


        for (let i = this.minValue; i <= this.maxValue; i++) {
            if (work[i].getSolutionSize() > 0) {
                //if (!work[i].fromCache) {
                //	work[i].determineLivingLocations(this.livingLocations, living.index);
                //}
            } else {
                work[i] = null;   // if no solutions then don't hold on to the details
            }

        }

        this.children = work;

    }


     compareTo(o) {

        // return location most likely to be clear  - this has to be first, the logic depends upon it
        let test = this.mineCount - o.mineCount;
        if (test != 0) {
            return test;
        }

        // then the location most likely to have a zero
        test = o.zeroSolutions - this.zeroSolutions;
        if (test != 0) {
            return test;
        }

        // then by most number of different possible values
        test = o.count - this.count;
        if (test != 0) {
            return test;
        }

        // then by the maxSolutions - ascending
        return this.maxSolutions - o.maxSolutions;

    }

}

/**
 * A representation of a possible state of the game
 */
class Node {

    constructor (position) {

        this.position;   // representation of the position we are analysing / have reached

        if (position == null) {
            this.position = new Position();
        } else {
            this.position = position;
        }

        this.livingLocations;       // these are the locations which need to be analysed

        this.winningLines = 0;      // this is the number of winning lines below this position in the tree
        this.work = 0;              // this is a measure of how much work was needed to calculate WinningLines value
        this.fromCache = false;     // indicates whether this position came from the cache

        this.startLocation;         // the first solution in the solution array that applies to this position
        this.endLocation;           // the last + 1 solution in the solution array that applies to this position

        this.bestLiving;            // after analysis this is the location that represents best play

    }

    getLivingLocations() {
        return this.livingLocations;
    }

    getSolutionSize() {
        return this.endLocation - this.startLocation;
    }

    /**
     * Get the probability of winning the game from the position this node represents  (winningLines / solution size)
      */
    getProbability() {

        return this.winningLines / this.getSolutionSize();

    }

    /**
     * Calculate the number of winning lines if this move is played at this position
     * Used at top of the game tree
     */
    getWinningLinesStart(move) {  // move is class LivingLocation 

        //if we can never exceed the cutoff then no point continuing
        if (BruteForceGlobal.PRUNE_BF_ANALYSIS && (this.getSolutionSize() - move.mineCount <= this.winningLines)) {
            move.pruned = true;
            return this.getSolutionSize() - move.mineCount;
        }

        var winningLines = this.getWinningLines(1, move, this.winningLines);

        if (winningLines > this.winningLines) {
            this.winningLines = winningLines;
        }

        return winningLines;
    }


    /**
     * Calculate the number of winning lines if this move is played at this position
     * Used when exploring the game tree
     */
    getWinningLines(depth, move, cutoff) {  // move is class 'LivingLocation' 

        //console.log("At depth " + depth + " cutoff=" + cutoff);

        let result = 0;

        BruteForceGlobal.processCount++;
        if (BruteForceGlobal.processCount > BruteForceGlobal.BRUTE_FORCE_ANALYSIS_MAX_NODES) {
            return 0;
        }

        let notMines = this.getSolutionSize() - move.mineCount;   // number of solutions (at this node) which don't have a mine at this location 

        // if the max possible winning lines is less than the current cutoff then no point doing the analysis
        if (BruteForceGlobal.PRUNE_BF_ANALYSIS && (result + notMines <= cutoff)) {
            move.pruned = true;
            return result + notMines;
        }

        move.buildChildNodes(this);

        for (let i = 0; i < move.children.length; i++) {

            const child = move.children[i];  // child is class 'Node'

            if (child == null) {
                continue;  // continue the loop but ignore this entry
            }

            if (child.fromCache) {  // nothing more to do, since we did it before
                this.work++;
            } else {

                child.determineLivingLocations(this.livingLocations, move.index);
                this.work++;

                if (child.getLivingLocations().length == 0) {  // no further information ==> all solution indistinguishable ==> 1 winning line

                    child.winningLines = 1;

                } else {  // not cached and not terminal node, so we need to do the recursion

                    for (let j = 0; j < child.getLivingLocations().length; j++) {

                        const childMove = child.getLivingLocations()[j];  // childmove is class 'LivingLocation'

                        // if the number of safe solutions <= the best winning lines then we can't do any better, so skip the rest
                        if (child.getSolutionSize() - childMove.mineCount <= child.winningLines) {
                            break;
                        }

                        // now calculate the winning lines for each of these children
                        const winningLines = child.getWinningLines(depth + 1, childMove, child.winningLines);
                        if (!childMove.pruned) {
                            if (child.winningLines < winningLines || (child.bestLiving != null && child.winningLines == winningLines && child.bestLiving.mineCount < childMove.mineCount)) {
                                child.winningLines = winningLines;
                                child.bestLiving = childMove;
                            }
                        }

                        // if there are no mines then this is a 100% safe move, so skip any further analysis since it can't be any better
                        if (childMove.mineCount == 0) {
                            break;
                        }


                    }

                    // no need to hold onto the living location once we have determined the best of them
                    child.livingLocations = null;

                    //add the child to the cache if it didn't come from there and it is carrying sufficient winning lines
                    if (child.work > 10) {
                        //console.log("Entry placed in cache with key " + child.position.hashCode());
                        child.work = 0;
                        child.fromCache = true;
                        BruteForceGlobal.cache.set(child.position.hashCode(), child);
                    } else {
                        this.work = this.work + child.work;
                    }


                }

            }

            if (depth > BruteForceGlobal.BRUTE_FORCE_ANALYSIS_TREE_DEPTH) {  // stop holding the tree beyond this depth
                child.bestLiving = null;
            }

            // store the aggregate winning lines 
            result = result + child.winningLines;

            notMines = notMines - child.getSolutionSize();  // reduce the number of not mines

            // if the max possible winning lines is less than the current cutoff then no point doing the analysis
            if (BruteForceGlobal.PRUNE_BF_ANALYSIS && (result + notMines <= cutoff)) {
                move.pruned = true;
                return result + notMines;
            }

        }

        return result;

    }

    /**
     * this generates a list of Location that are still alive, (i.e. have more than one possible value) from a list of previously living locations
     * Index is the move which has just been played (in terms of the off-set to the position[] array)
     */
    determineLivingLocations(liveLocs, index) {  // liveLocs is a array of class 'LivingLocation' 

        const living = [];

        for (let i = 0; i < liveLocs.length; i++) {

            const live = liveLocs[i];

            if (live.index == index) {  // if this is the same move we just played then no need to analyse it - definitely now non-living.
                continue;
            }

            let value;

            const valueCount = Array(9).fill(0);
            let mines = 0;
            let maxSolutions = 0;
            let count = 0;
            let minValue = 0;
            let maxValue = 0;

            for (let j = this.startLocation; j < this.endLocation; j++) {
                value = BruteForceGlobal.allSolutions.get(j)[live.index];
                if (value != BOMB) {
                     valueCount[value]++;
                } else {
                    mines++;
                }
            }

            // find the new minimum value and maximum value for this location (can't be wider than the previous min and max)
            for (let j = live.minValue; j <= live.maxValue; j++) {
                if (valueCount[j] > 0) {
                    if (count == 0) {
                        minValue = j;
                    }
                    maxValue = j;
                    count++;
                    if (maxSolutions < valueCount[j]) {
                        maxSolutions = valueCount[j];
                    }
                }
            }
            if (count > 1) {
                const alive = new LivingLocation(live.index);  // alive is class 'LivingLocation'
                alive.mineCount = mines;
                alive.count = count;
                alive.minValue = minValue;
                alive.maxValue = maxValue;
                alive.maxSolutions = maxSolutions;
                alive.zeroSolutions = valueCount[0];
                living.push(alive);
            }

        }

        living.sort((a, b) => a.compareTo(b));

        this.livingLocations = living;

    }

}

// used to hold all the solutions left in the game
class SolutionTable {

    constructor(solutions) {
        this.solutions = solutions;
    }

    get(index) {
        return this.solutions[index];
    }

    size() {
        return this.solutions.length;
    }

    sortSolutions(start, end, index) {

        const section = this.solutions.slice(start, end);
        section.sort((a, b) => a[index] - b[index]);
        this.solutions.splice(start, section.length, ...section);


        //subSort(this.solutions, start, end - start + 1, (a, b) => b[index] - a[index]);

        //this.solutions.sort(solutions, start, end, sorters[index]);

    }

}

// utility to sort an array 
let subSort = (arr, i, n, sortFx) => [].concat(...arr.slice(0, i), ...arr.slice(i, i + n).sort(sortFx), ...arr.slice(i + n, arr.length));

/**
 *  Performs a brute force search on the provided squares using the iterator 
 * 
 */
class Cruncher {

    constructor(board, iterator) {

        this.board = board;
        this.iterator = iterator;   // the iterator
        this.tiles = iterator.tiles;  // the tiles the iterator is iterating over
        this.witnesses = iterator.probabilityEngine.dependentWitnesses;  // the dependent witnesses (class BoxWitness) which need to be checked to see if they are satisfied

        this.allSolutions = [];  // this is where the solutions needed by the Brute Force Analysis class are held

        // determine how many flags are currently next to each tile
        this.currentFlagsTiles = [];
        for (let i = 0; i < this.tiles.length; i++) {
            this.currentFlagsTiles.push(board.adjacentFoundMineCount(this.tiles[i]));
        }

        // determine how many flags are currently next to each witness
        this.currentFlagsWitnesses = [];
        for (let i = 0; i < this.witnesses.length; i++) {
            this.currentFlagsWitnesses.push(board.adjacentFoundMineCount(this.witnesses[i].tile));
        }

        this.duration = 0;

    }


    
    crunch() {

        const peStart = Date.now();

        let sample = this.iterator.getSample();  // first sample

        let candidates = 0;  // number of samples which satisfy the current board state

        while (sample != null) {

            if (this.checkSample(sample)) {
                candidates++;
            }

            sample = this.iterator.getSample();

        }

        this.duration = Date.now() - peStart;

        console.log(this.iterator.iterationsDone + " cycles took " + this.duration + " milliseconds");

        return candidates;

    }

    // this checks whether the positions of the mines are a valid candidate solution
    checkSample(sample) {

        // get the tiles which are mines in this sample
        const mine = [];
        for (let i = 0; i < sample.length; i++) {
            mine.push(this.tiles[sample[i]]);
        }

        for (let i = 0; i < this.witnesses.length; i++) {

            const flags1 = this.currentFlagsWitnesses[i];
            let flags2 = 0;

            // count how many candidate mines are next to this witness
            for (let j = 0; j < mine.length; j++) {
                if (mine[j].isAdjacent(this.witnesses[i].tile)) {
                    flags2++;
                }
            }

            const value = this.witnesses[i].tile.getValue();  // number of flags indicated on the tile

            if (value != flags1 + flags2) {
                return false;
            }
        }

        //if it is a good solution then calculate the distribution if required

        const solution = new Array(this.tiles.length);

        for (let i = 0; i < this.tiles.length; i++) {

            let isMine = false;
            for (let j = 0; j < sample.length; j++) {
                if (i == sample[j]) {
                    isMine = true;
                    break;
                }
            }

            // if we are a mine then it doesn't matter how many mines surround us
            if (!isMine) {
                var flags2 = this.currentFlagsTiles[i];
                // count how many candidate mines are next to this square
                for (let j = 0; j < mine.length; j++) {
                    if (mine[j].isAdjacent(this.tiles[i])) {
                        flags2++;
                    }
                }
                solution[i] = flags2;
            } else {
                solution[i] = BOMB;
            }

        }
 
        this.allSolutions.push(solution);

        /*
        var output = "";
        for (var i = 0; i < mine.length; i++) {
            output = output + mine[i].asText();
        }
        console.log(output);
        */

        return true;

    }
    
}

class WitnessWebIterator {

    // create an iterator which is like a set of rotating wheels
    // if rotation is -1 then this does all the possible iterations
    // if rotation is not - 1 then this locks the first 'cog' in that position and iterates the remaining cogs.  This allows parallel processing based on the position of the first 'cog'
    constructor(pe, allCoveredTiles, rotation) {

        console.log("Creating Iterator");

        let BINOMIAL = new Binomial(50000, 200);

        this.sample = [];  // int array

        this.tiles = [];  // list of tiles being iterated over

        this.cogs = []; // array of cogs
        this.squareOffset = [];  // int array
        this.mineOffset = [];   // int array

        this.iterationsDone = 0;

        this.top;
        this.bottom;

        this.done = false;

        this.probabilityEngine = pe;

        this.cycles = BigInt(1);

        // if we are setting the position of the top cog then it can't ever change
        if (rotation == -1) {
            this.bottom = 0;
        } else {
            this.bottom = 1;
        }

        //cogs = new SequentialIterator[this.probabilityEngine..size() + 1];
        //squareOffset = new int[web.getIndependentWitnesses().size() + 1];
        //mineOffset = new int[web.getIndependentWitnesses().size() + 1];
 
        const loc = [];  // array of locations

        var indWitnesses = this.probabilityEngine.independentWitnesses;

        var cogi = 0;
        let indSquares = 0;
        let indMines = 0;

        // create an array of locations in the order of independent witnesses
        for (let i = 0; i < indWitnesses.length; i++) {

            const w = indWitnesses[i];

            this.squareOffset.push(indSquares);
            this.mineOffset.push(indMines);
            this.cogs.push(new SequentialIterator(w.minesToFind, w.tiles.length));
 
            indSquares = indSquares + w.tiles.length;
            indMines = indMines + w.minesToFind;

            loc.push(...w.tiles);

            // multiply up the number of iterations needed
            this.cycles = this.cycles * BINOMIAL.combination(w.minesToFind, w.tiles.length);

        }

        //System.out.println("Mines left = " + (mines - indMines));
        //System.out.println("Squrs left = " + (web.getSquares().length - indSquares));

        // the last cog has the remaining squares and mines

        //add the rest of the locations
        for (let i = 0; i < allCoveredTiles.length; i++) {

            const l = allCoveredTiles[i];

            var skip = false;
            for (let j = 0; j < loc.length; j++) {

                const m = loc[j];

                if (l.isEqual(m)) {
                    skip = true;
                    break;
                }
            }
            if (!skip) {
                loc.push(l);
            }
        }

        this.tiles = loc;

        console.log("Mines left " + this.probabilityEngine.minesLeft);
        console.log("Independent Mines " + indMines);
        console.log("Tiles left " + this.probabilityEngine.tilesLeft);
        console.log("Independent tiles " + indSquares);


        // if there are more mines left then squares then no solution is possible
        // if there are not enough mines to satisfy the minimum we know are needed
        if (this.probabilityEngine.minesLeft - indMines > this.probabilityEngine.tilesLeft - indSquares
            || indMines > this.probabilityEngine.minesLeft) {
            this.done = true;
            this.top = 0;
            console.log("Nothing to do in this iterator");
            return;
        }

        // if there are no mines left then no need for a cog
        if (this.probabilityEngine.minesLeft > indMines) {
            this.squareOffset.push(indSquares);
            this.mineOffset.push(indMines);
            this.cogs.push(new SequentialIterator(this.probabilityEngine.minesLeft - indMines, this.probabilityEngine.tilesLeft - indSquares));

            this.cycles = this.cycles * BINOMIAL.combination(this.probabilityEngine.minesLeft - indMines, this.probabilityEngine.tilesLeft - indSquares);
        }

        this.top = this.cogs.length - 1;

        this.sample = new Array(this.probabilityEngine.minesLeft);  // make the sample array the size of the number of mines

        // if we are locking and rotating the top cog then do it
        //if (rotation != -1) {
        //    for (var i = 0; i < rotation; i++) {
        //        this.cogs[0].getSample(0);
        //    }
        //}

        // now set up the initial sample position
        for (let i = 0; i < this.top; i++) {
            const s = this.cogs[i].getNextSample();
            for (let j = 0; j < s.length; j++) {
                this.sample[this.mineOffset[i] + j] = this.squareOffset[i] + s[j];
            }
        }

        console.log("Iterations needed " + this.cycles);
 
    }


    getSample() {


        if (this.done) {
            console.log("**** attempting to iterator when already completed ****");
            return null;
        }
        let index = this.top;

        let s = this.cogs[index].getNextSample();

        while (s == null && index != this.bottom) {
            index--;
            s = this.cogs[index].getNextSample();
        }

        if (index == this.bottom && s == null) {
            this.done = true;
            return null;
        }

        for (let j = 0; j < s.length; j++) {
            this.sample[this.mineOffset[index] + j] = this.squareOffset[index] + s[j];
        }
        index++;
        while (index <= this.top) {
            this.cogs[index] = new SequentialIterator(this.cogs[index].numberBalls, this.cogs[index].numberHoles);
            s = this.cogs[index].getNextSample();
            for (let j = 0; j < s.length; j++) {
                this.sample[this.mineOffset[index] + j] = this.squareOffset[index] + s[j];
            }
            index++;
        }

         //console.log(...this.sample);

        this.iterationsDone++;

        return this.sample;
 
    }

    getTiles() {
        return this.allCoveredTiles;
    }

    getIterations() {
        return this.iterationsDone;
    }

    // if the location is a Independent witness then we know it will always
    // have exactly the correct amount of mines around it since that is what
    // this iterator does
    witnessAlwaysSatisfied(location) {

        for (let i = 0; i < this.probabilityEngine.independentWitness.length; i++) {
            if (this.probabilityEngine.independentWitness[i].equals(location)) {
                return true;
            }
        }

        return false;

    }

}

class SequentialIterator {


    // a sequential iterator that puts n-balls in m-holes once in each possible way
    constructor (n, m) {

        this.numberHoles = m;
        this.numberBalls = n;

        this.sample = [];  // integer

        this.more = true;

        this.index = n - 1;

        for (let i = 0; i < n; i++) {
            this.sample.push(i);
        }

        // reduce the iterator by 1, since the first getSample() will increase it
        // by 1 again
        this.sample[this.index]--;

        //console.log("Sequential Iterator has " + this.numberBalls + " mines and " + this.numberHoles + " squares");

    }

    getNextSample() {

        if (!this.more) {
            console.log("****  Trying to iterate after the end ****");
            return null;
        }

        this.index = this.numberBalls - 1;

        // add on one to the iterator
        this.sample[this.index]++;

        // if we have rolled off the end then move backwards until we can fit
        // the next iteration
        while (this.sample[this.index] >= this.numberHoles - this.numberBalls + 1 + this.index) {
            if (this.index == 0) {
                this.more = false;
                return null;
            } else {
                this.index--;
                this.sample[this.index]++;
            }
        }

        // roll forward 
        while (this.index != this.numberBalls - 1) {
            this.index++;
            this.sample[this.index] = this.sample[this.index - 1] + 1;
        }

        return this.sample;

    }

}

class MergeSorter {

    constructor(boxes) {

        if (boxes == null) {
            this.checks = [];
            return;
        }

        this.checks = Array(boxes.length);

        for (let i = 0; i < boxes.length; i++) {
            this.checks[i] = boxes[i].uid;
        }

    }

    compare(p1, p2) {

        let c = p1.mineCount - p2.mineCount;

        if (c != 0) {
            return c;
        }

        for (let i = 0; i < this.checks.length; i++) {
            const index = this.checks[i];

            c = p1.allocatedMines[index] - p2.allocatedMines[index];

            if (c != 0) {
                return c;
            }

        }

        return 0;
    }
		
}

/*
 * Used to hold a solution
 */
class ProbabilityLine {

	constructor(boxCount, solutionCount) {
		
        this.mineCount = 0;
        if (solutionCount == null) {
            this.solutionCount = BigInt(0);
        } else {
            this.solutionCount = solutionCount;
        }
        
        this.mineBoxCount = Array(boxCount).fill(BigInt(0));
        this.allocatedMines = Array(boxCount).fill(0);

    }
	
}

// used to hold what we need to analyse next
class NextWitness {
    constructor(boxWitness) {

        this.boxWitness = boxWitness;

        this.oldBoxes = [];
        this.newBoxes = [];

        for (let i = 0; i < this.boxWitness.boxes.length; i++) {

            const box = this.boxWitness.boxes[i];
            if (box.processed) {
                this.oldBoxes.push(box);
            } else {
                this.newBoxes.push(box);
            }
        }
    }

}

// holds a witness and all the Boxes adjacent to it
class BoxWitness {
	constructor(board, tile) {

        this.tile = tile;

        this.boxes = [];  // adjacent boxes 
        this.tiles = [];  // adjacent tiles

        this.processed = false;
        this.minesToFind = tile.getValue();   

        const adjTile = board.getAdjacent(tile);

        // determine how many mines are left to find and store adjacent tiles
        for (let i = 0; i < adjTile.length; i++) {
            if (adjTile[i].isSolverFoundBomb()) {
                this.minesToFind--;
            } else if (adjTile[i].isCovered()) {
                this.tiles.push(adjTile[i]);
            }
        }		
 	}

    overlap(boxWitness) {

        // if the locations are too far apart they can't share any of the same squares
        if (Math.abs(boxWitness.tile.x - this.tile.x) > 2 || Math.abs(boxWitness.tile.y - this.tile.y) > 2) {
            return false;
        }

        top: for (let i = 0; i < boxWitness.tiles.length; i++) {

            const tile1 = boxWitness.tiles[i];

            for (let j = 0; j < this.tiles.length; j++) {

                const tile2 = this.tiles[j];

                if (tile1.isEqual(tile2)) {  // if they share a tile then return true
                    return true;
                }
            }
        }

        // no shared tile found
        return false;

    }


    // if two witnesses have the same Squares around them they are equivalent
    equivalent(boxWitness) {

        // if the number of squares is different then they can't be equivalent
        if (this.tiles.length != boxWitness.tiles.length) {
            return false;
        }

        // if the locations are too far apart they can't share the same squares
        if (Math.abs(boxWitness.tile.x - this.tile.x) > 2 || Math.abs(boxWitness.tile.y - this.tile.y) > 2) {
            return false;
        }

        for (let i = 0; i < this.tiles.length; i++) {

            const l1 = this.tiles[i];

            let found = false;
            for (let j = 0; j < boxWitness.tiles.length; j++) {
                if (boxWitness.tiles[j].index == l1.index) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }

        return true;
    }

    // add an adjacdent box 
    addBox(box) {
        this.boxes.push(box);
    }
}

// information about the boxes surrounding a dead candidate
class DeadCandidate {

    constructor() {

        this.candidate;
        this.myBox;
        this.isAlive = false;
        this.goodBoxes = [];
        this.badBoxes = [];

        this.firstCheck = true;
        this.total = 0;

    }

}

// a box is a group of tiles which share the same witnesses
class Box {
	constructor(boxWitnesses, tile, uid) {

        this.processed = false;

		this.uid = uid;
        this.minMines;
        this.maxMines;

        this.tiles = [tile];

        // this is used to indicate how many tiles in the box must not contain mine.
        this.emptyTiles = 0;
		
		this.boxWitnesses = [];

        this.mineTally = BigInt(0);

		for (let i=0; i < boxWitnesses.length; i++) {
			if (tile.isAdjacent(boxWitnesses[i].tile)) {
                this.boxWitnesses.push(boxWitnesses[i]);
                boxWitnesses[i].addBox(this);

			}
		}
		
		//console.log("Box created for tile " + tile.asText() + " with " + this.boxWitnesses.length + " witnesses");

	}
	
	// if the tiles surrounding witnesses equal the boxes then it fits
	fits(tile, count) {

		// a tile can't share the same witnesses for this box if they have different numbers
		if (count != this.boxWitnesses.length) {
			return false;
		}
		
		for (let i=0; i < this.boxWitnesses.length; i++) {
			if (!this.boxWitnesses[i].tile.isAdjacent(tile)) {
				return false;
			}
		}		
		
		//console.log("Tile " + tile.asText() + " fits in box with tile " + this.tiles[0].asText());
		
		return true;
		
	}

    /*
    * Once all the squares have been added we can do some calculations
    */
    calculate(minesLeft) {

        this.maxMines = Math.min(this.tiles.length, minesLeft);  // can't have more mines then there are tiles to put them in or mines left to discover
        this.minMines = 0;

        for (let i = 0; i < this.boxWitnesses.length; i++) {
            if (this.boxWitnesses[i].minesToFind < this.maxMines) {  // can't have more mines than the lowest constraint
                this.maxMines = this.boxWitnesses[i].minesToFind;
            }
        }		

    }

    incrementEmptyTiles() {

        this.emptyTiles++;
        if (this.maxMines > this.tiles.length - this.emptyTiles) {
            this.maxMines = this.tiles.length - this.emptyTiles;
        }

    }

	// add a new tile to the box
	add(tile) {
		this.tiles.push(tile);
	}

    contains(tile) {

        // return true if the given tile is in this box
        for (let i = 0; i < this.tiles.length; i++) {
            if (this.tiles[i].index == tile.index) {
                return true;
            }
        }

        return false;

    }

}

// Links which when joined together might form a 50/50 chain
class Link {

    constructor() {

        this.tile1;
        this.closed1 = true;
        this.tile2;
        this.closed2 = true;

        this.processed = false;

        this.trouble = [];
    }

}

class SolutionCounter {

    static SMALL_COMBINATIONS = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1], [1, 5, 10, 10, 5, 1], [1, 6, 15, 20, 15, 6, 1], [1, 7, 21, 35, 35, 21, 7, 1], [1, 8, 28, 56, 70, 56, 28, 8, 1]];

	constructor(board, allWitnesses, allWitnessed, squaresLeft, minesLeft) {

        this.board = board;

		//this.witnesses = allWitnesses;
		this.witnessed = allWitnessed;

        this.prunedWitnesses = [];  // a subset of allWitnesses with equivalent witnesses removed

        // constraints in the game
        this.minesLeft = minesLeft;
        //this.tilesLeft = squaresLeft;
        this.tilesOffEdge = squaresLeft - allWitnessed.length;   // squares left off the edge and unrevealed
        this.minTotalMines = minesLeft - this.tilesOffEdge;   // //we can't use so few mines that we can't fit the remainder elsewhere on the board
        this.maxTotalMines = minesLeft;

        this.boxes = [];
        this.boxWitnesses = [];
        this.mask = [];

		this.workingProbs = []; 
        this.heldProbs = [];
        this.offEdgeMineTally = BigInt(0);
        this.finalSolutionsCount = BigInt(0);
        this.clearCount = 0;
        this.localClears = [];

        this.validWeb = true;

        this.recursions = 0;

        // can't have less than zero mines
        if (minesLeft < 0) {
            this.validWeb = false;
            return;
        }

        // generate a BoxWitness for each witness tile and also create a list of pruned witnesses for the brute force search
        var pruned = 0;
        for (var i = 0; i < allWitnesses.length; i++) {
            var wit = allWitnesses[i];

            var boxWit = new BoxWitness(this.board, wit);

            // can't have too many or too few mines 
            if (boxWit.minesToFind < 0 || boxWit.minesToFind > boxWit.tiles.length) {
                this.validWeb = false;
            }

            // if the witness is a duplicate then don't store it
            var duplicate = false;
            for (var j = 0; j < this.boxWitnesses.length; j++) {

                var w = this.boxWitnesses[j];

                if (w.equivalent(boxWit)) {
                    duplicate = true;
                    break;
                }
            }
            if (!duplicate) {
                this.prunedWitnesses.push(boxWit);
             } else {
                pruned++;
            }
            this.boxWitnesses.push(boxWit);  // all witnesses are needed for the probability engine
        }
        //console.log("Pruned " + pruned + " witnesses as duplicates");
        //console.log("There are " + this.boxWitnesses.length + " Box witnesses");

		// allocate each of the witnessed squares to a box
		var uid = 0;
		for (var i=0; i < this.witnessed.length; i++) {
			
			var tile = this.witnessed[i];
			
			var count = 0;
			
			// count how many adjacent witnesses the tile has
			for (var j=0; j < allWitnesses.length; j++) {
				if (tile.isAdjacent(allWitnesses[j])) {
					count++;
				}
			}
			
            // see if the witnessed tile fits any existing boxes
            var found = false;
			for (var j=0; j < this.boxes.length; j++) {
				
				if (this.boxes[j].fits(tile, count)) {
					this.boxes[j].add(tile);
					found = true;
					break;
				}
				
			}
			
			// if not found create a new box and store it
			if (!found) {
                this.boxes.push(new Box(this.boxWitnesses, tile, uid++));
			}

        }

        // calculate the min and max mines for each box 
        for (var i = 0; i < this.boxes.length; i++) {
            var box = this.boxes[i];
            box.calculate(this.minesLeft);
            //console.log("Box " + box.tiles[0].asText() + " has min mines = " + box.minMines + " and max mines = " + box.maxMines);
        }

        // Report how many boxes each witness is adjacent to 
        for (var i = 0; i < this.boxWitnesses.length; i++) {
            var boxWit = this.boxWitnesses[i];
            //console.log("Witness " + boxWit.tile.asText() + " is adjacent to " + boxWit.boxes.length + " boxes and has " + boxWit.minesToFind + " mines to find");
        }

        Object.seal(this) // prevent new properties being created
 	}


    // calculate a probability for each un-revealed tile on the board
	process() {

        // if the board isn't valid then solution count is zero
        if (!this.validWeb) {
            console.log("Web is invalid");
            this.finalSolutionsCount = BigInt(0);
            this.clearCount = 0;
            return;
        }

        // create an array showing which boxes have been procesed this iteration - none have to start with
        this.mask = Array(this.boxes.length).fill(false);

		// create an initial solution of no mines anywhere 
        this.heldProbs.push(new ProbabilityLine(this.boxes.length, BigInt(1)));
		
		// add an empty probability line to get us started
        this.workingProbs.push(new ProbabilityLine(this.boxes.length, BigInt(1)));
		
        var nextWitness = this.findFirstWitness();

        while (nextWitness != null) {

            //console.log("Solution counter processing witness " + nextWitness.boxWitness.tile.asText());

            // mark the new boxes as processed - which they will be soon
            for (var i = 0; i < nextWitness.newBoxes.length; i++) {
                this.mask[nextWitness.newBoxes[i].uid] = true;
            }

            this.workingProbs = this.mergeProbabilities(nextWitness);

            nextWitness = this.findNextWitness(nextWitness);

        }

        //this.calculateBoxProbabilities();

        // if this isn't a valid board than nothing to do
        if (this.heldProbs.length != 0) {
            this.calculateBoxProbabilities();
        } else {
            this.finalSolutionsCount = BigInt(0);
            this.clearCount = 0;
        }
  		
	}


    // take the next witness details and merge them into the currently held details
    mergeProbabilities(nw) {

        var newProbs = [];

        for (var i = 0; i < this.workingProbs.length; i++) {

            var pl = this.workingProbs[i];

            var missingMines = nw.boxWitness.minesToFind - this.countPlacedMines(pl, nw);

            if (missingMines < 0) {
                //console.log("Missing mines < 0 ==> ignoring line");
                // too many mines placed around this witness previously, so this probability can't be valid
            } else if (missingMines == 0) {
                //console.log("Missing mines = 0 ==> keeping line as is");
                newProbs.push(pl);   // witness already exactly satisfied, so nothing to do
            } else if (nw.newBoxes.length == 0) {
                //console.log("new boxes = 0 ==> ignoring line since nowhere for mines to go");
                // nowhere to put the new mines, so this probability can't be valid
            } else {
                
                var result = this.distributeMissingMines(pl, nw, missingMines, 0);
                newProbs.push(...result);
            }

        }

        // flag the last set of details as processed
        nw.boxWitness.processed = true;

        for (var i = 0; i < nw.newBoxes.length; i++) {
            nw.newBoxes[i].processed = true;
        }

        var boundaryBoxes = [];
        for (var i = 0; i < this.boxes.length; i++) {
            var box = this.boxes[i];
            var notProcessed = false;
            var processed = false;
            for (var j = 0; j < box.boxWitnesses.length; j++) {
                if (box.boxWitnesses[j].processed) {
                    processed = true;
                } else {
                    notProcessed = true;
                }
                if (processed && notProcessed) {
                    //boardState.display("partially processed box " + box.getUID());
                    boundaryBoxes.push(box);
                    break;
                }
            }
        }
        //boardState.display("Boxes partially processed " + boundaryBoxes.size());

        var sorter = new MergeSorter(boundaryBoxes);

        newProbs = this.crunchByMineCount(newProbs, sorter);

        return newProbs;

    }

    // counts the number of mines already placed
    countPlacedMines(pl, nw) {

        var result = 0;

        for (var i = 0; i < nw.oldBoxes.length; i++) {

            var b = nw.oldBoxes[i];

            result = result + pl.allocatedMines[b.uid];
        }

        return result;
    }

    // this is used to recursively place the missing Mines into the available boxes for the probability line
    distributeMissingMines(pl, nw,  missingMines, index) {

        //console.log("Distributing " + missingMines + " missing mines to box " + nw.newBoxes[index].uid);

        this.recursions++;
        if (this.recursions % 1000 == 0) {
            console.log("Solution Counter recursision = " + this.recursions);
        }

        var result = [];

        // if there is only one box left to put the missing mines we have reach the end of this branch of recursion
        if (nw.newBoxes.length - index == 1) {
            // if there are too many for this box then the probability can't be valid
            if (nw.newBoxes[index].maxMines < missingMines) {
                //console.log("Abandon (1)");
                return result;
            }
            // if there are too few for this box then the probability can't be valid
            if (nw.newBoxes[index].minMines > missingMines) {
                //console.log("Abandon (2)");
                return result;
            }
            // if there are too many for this game then the probability can't be valid
            if (pl.mineCount + missingMines > this.maxTotalMines) {
                //console.log("Abandon (3)");
                return result;
            }

            result.push(this.extendProbabilityLine(pl, nw.newBoxes[index], missingMines));
            //console.log("Distribute missing mines line after " + pl.mineBoxCount);
            return result;
        }


        // this is the recursion
        var maxToPlace = Math.min(nw.newBoxes[index].maxMines, missingMines);

        for (var i = nw.newBoxes[index].minMines; i <= maxToPlace; i++) {
            var npl = this.extendProbabilityLine(pl, nw.newBoxes[index], i);

            var r1 = this.distributeMissingMines(npl, nw, missingMines - i, index + 1);
            result.push(...r1);

        }

        return result;

    }

    // create a new probability line by taking the old and adding the mines to the new Box
    extendProbabilityLine(pl, newBox, mines) {

        //console.log("Extended probability line: Adding " + mines + " mines to box " + newBox.uid);
        //console.log("Extended probability line before" + pl.mineBoxCount);

        // there are less ways to place the mines if we know one of the tiles doesn't contain a mine
        const modifiedTilesCount = newBox.tiles.length - newBox.emptyTiles;

        //var combination = SolutionCounter.SMALL_COMBINATIONS[newBox.tiles.length][mines];
        var combination = SolutionCounter.SMALL_COMBINATIONS[modifiedTilesCount][mines];
        var bigCom = BigInt(combination);

        var newSolutionCount = pl.solutionCount * bigCom;

        var result = new ProbabilityLine(this.boxes.length, newSolutionCount);

        result.mineCount = pl.mineCount + mines;
        //result.solutionCount = pl.solutionCount;

        // copy the probability array

        if (combination != 1) {
            for (var i = 0; i < pl.mineBoxCount.length; i++) {
                result.mineBoxCount[i] = pl.mineBoxCount[i] * bigCom;
            }
        } else {
            result.mineBoxCount = pl.mineBoxCount.slice();
        }

        result.mineBoxCount[newBox.uid] = BigInt(mines) * result.solutionCount;

        result.allocatedMines = pl.allocatedMines.slice();
        result.allocatedMines[newBox.uid] = mines;

        //console.log("Extended probability line after " + result.mineBoxCount);

        return result;
    }


    // this combines newly generated probabilities with ones we have already stored from other independent sets of witnesses
    storeProbabilities() {

        //console.log("At store probabilities");

        var result = [];

        if (this.workingProbs.length == 0) {
            //console.log("working probabilites list is empty!!");
            this.heldProbs = [];
        	return;
        } 

        // crunch the new ones down to one line per mine count
        //var crunched = this.crunchByMineCount(this.workingProbs);

        var crunched = this.workingProbs;

        //solver.display("New data has " + crunched.size() + " entries");

        for (var i = 0; i < crunched.length; i++) {

            pl = crunched[i];

            for (var j = 0; j < this.heldProbs.length; j++) {

                var epl = this.heldProbs[j];

                var npl = new ProbabilityLine(this.boxes.length);

                npl.mineCount = pl.mineCount + epl.mineCount;

                if (npl.mineCount <= this.maxTotalMines) {

                    npl.solutionCount = pl.solutionCount * epl.solutionCount;

                    for (var k = 0; k < npl.mineBoxCount.length; k++) {

                        var w1 = pl.mineBoxCount[k] * epl.solutionCount;
                        var w2 = epl.mineBoxCount[k] * pl.solutionCount;
                        npl.mineBoxCount[k] = w1 + w2;

                    }
                    result.push(npl);

                }
            }
        }

        // sort into mine order 
        result.sort(function (a, b) { return a.mineCount - b.mineCount });

        this.heldProbs = [];

        // if result is empty this is an impossible position
        if (result.length == 0) {
            return;
        }

        // and combine them into a single probability line for each mine count
        var mc = result[0].mineCount;
        var npl = new ProbabilityLine(this.boxes.length);
        npl.mineCount = mc;

        for (var i = 0; i < result.length; i++) {

            var pl = result[i];

            if (pl.mineCount != mc) {
                this.heldProbs.push(npl);
                mc = pl.mineCount;
                npl = new ProbabilityLine(this.boxes.length);
                npl.mineCount = mc;
            }
            npl.solutionCount = npl.solutionCount + pl.solutionCount;

            for (var j = 0; j < pl.mineBoxCount.length; j++) {
                npl.mineBoxCount[j] = npl.mineBoxCount[j] + pl.mineBoxCount[j];
            }
        }

        this.heldProbs.push(npl);


    }

    crunchByMineCount(target, sorter) {

        if (target.length == 0) {
            return target;
         }

        // sort the solutions by number of mines
        target.sort(function (a, b) { return sorter.compare(a,b) });

        var result = [];

        var current = null;

        for (var i = 0; i < target.length; i++) {

            var pl = target[i];

            if (current == null) {
                current = target[i];
            } else if (sorter.compare(current, pl) != 0) {
                result.push(current);
                current = pl;
            } else {
                this.mergeLineProbabilities(current, pl);
            }

        }

        //if (npl.mineCount >= minTotalMines) {
        result.push(current);
        //}	

        //console.log(target.length + " Probability Lines compressed to " + result.length); 

        return result;

    }

    // calculate how many ways this solution can be generated and roll them into one
    mergeLineProbabilities(npl, pl) {

        npl.solutionCount = npl.solutionCount + pl.solutionCount;

        for (var i = 0; i < pl.mineBoxCount.length; i++) {
            if (this.mask[i]) {  // if this box has been involved in this solution - if we don't do this the hash gets corrupted by boxes = 0 mines because they weren't part of this edge
                npl.mineBoxCount[i] = npl.mineBoxCount[i] + pl.mineBoxCount[i];
            }

        }

    }

    // return any witness which hasn't been processed
    findFirstWitness() {

        for (var i = 0; i < this.boxWitnesses.length; i++) {
            var boxWit = this.boxWitnesses[i];
            if (!boxWit.processed) {
                return new NextWitness(boxWit);
            }
        }

        return null;
    }

    // look for the next witness to process
    findNextWitness(prevWitness) {

        var bestTodo = 99999;
        var bestWitness = null;

        // and find a witness which is on the boundary of what has already been processed
        for (var i = 0; i < this.boxes.length; i++) {
            var b = this.boxes[i];
            if (b.processed) {
                for (var j = 0; j < b.boxWitnesses.length; j++) {
                    var w = b.boxWitnesses[j];
                    if (!w.processed) {
                        var todo = 0;
                        for (var k = 0; k < w.boxes.length; k++) {
                            var b1 = w.boxes[k];

                            if (!b1.processed) {
                                todo++;
                            }
                        }
                        if (todo == 0) {    // prioritise the witnesses which have the least boxes left to process
                            return new NextWitness(w);
                        } else if (todo < bestTodo) {
                            bestTodo = todo;
                            bestWitness = w;
                        }
                    }
                }
            }
        }

        if (bestWitness != null) {
            return new NextWitness(bestWitness);
        }

        // if we are down here then there is no witness which is on the boundary, so we have processed a complete set of independent witnesses 


        // since we have calculated all the mines in an independent set of witnesses we can crunch them down and store them for later

        // get an unprocessed witness
        var nw = this.findFirstWitness();

        this.storeProbabilities();

        // reset the working array so we can start building up one for the new set of witnesses
        this.workingProbs = [];
        this.workingProbs.push(new ProbabilityLine(this.boxes.length, BigInt(1)));

        // reset the mask indicating that no boxes have been processed 
        this.mask.fill(false);

        // if the position is invalid exit now
        if (this.heldProbs.length == 0) {
            return null;
        }

        // return the next witness to process
        return nw;

    }

    // here we expand the localised solution to one across the whole board and
    // sum them together to create a definitive probability for each box
    calculateBoxProbabilities() {

        let BINOMIAL = new Binomial(50000, 200);

        const emptyBox = Array(this.boxes.length).fill(true);

        // total game tally
        let totalTally = BigInt(0);

        // outside a box tally
        let outsideTally = BigInt(0);

        //console.log("There are " + this.heldProbs.length + " different mine counts on the edge");

        // calculate how many mines 
        for (let i = 0; i < this.heldProbs.length; i++) {

            const pl = this.heldProbs[i];

            //console.log("Mine count is " + pl.mineCount + " with solution count " + pl.solutionCount + " mineBoxCount = " + pl.mineBoxCount);

            if (pl.mineCount >= this.minTotalMines) {    // if the mine count for this solution is less than the minimum it can't be valid

                //console.log("Mines left " + this.minesLeft + " mines on PL " + pl.mineCount + " squares left = " + this.squaresLeft);
                var mult = BINOMIAL.combination(this.minesLeft - pl.mineCount, this.tilesOffEdge);  //# of ways the rest of the board can be formed

                outsideTally = outsideTally + mult * BigInt(this.minesLeft - pl.mineCount) * (pl.solutionCount);

                // this is all the possible ways the mines can be placed across the whole game
                totalTally = totalTally + mult * (pl.solutionCount);

                for (let j = 0; j < emptyBox.length; j++) {
                    if (pl.mineBoxCount[j] != 0) {
                        emptyBox[j] = false;
                    }
                }
            }

        }

        // count how many clears we have
        if (totalTally > 0) {
            for (let i = 0; i < this.boxes.length; i++) {
                if (emptyBox[i]) {
                    this.clearCount = this.clearCount + this.boxes[i].tiles.length;
                    this.localClears.push(...this.boxes[i].tiles);
                 }
            }
        }

        if (this.tilesOffEdge != 0) {
            this.offEdgeMineTally = outsideTally / BigInt(this.tilesOffEdge);
        } else {
            this.offEdgeMineTally = 0;
        }
 
        this.finalSolutionsCount = totalTally;

         //console.log("Game has  " + this.finalSolutionsCount + " candidate solutions and " + this.clearCount + " clears");

    }

    // forces a box to contain a tile which isn't a mine.  If the location isn't in a box then reduce the off edge details.

    setMustBeEmpty(tile) {

        const box = this.getBox(tile);

        if (box == null) {  // if the tiles isn't on the edge then adjust the off edge values
            this.tilesOffEdge--;
            this.minTotalMines = Math.max(0, this.minesLeft - this.tilesOffEdge);

            //this.validWeb = false;
            //return false;
        } else if (box.minMines != 0) {
            this.validWeb = false;
            return false;

        } else {
            box.incrementEmptyTiles();
        }

        return true;

    }

    // get the box containing this tile
    getBox(tile) {

        for (var i = 0; i < this.boxes.length; i++) {
            if (this.boxes[i].contains(tile)) {
                return this.boxes[i];
            }
        }

        return null;
    }

    getLocalClears() {
        return this.localClears;
    }

}

class EfficiencyHelper {

    static ALLOW_ZERO_NET_GAIN_CHORD = true;
    static ALLOW_ZERO_NET_GAIN_PRE_CHORD = true;

    constructor(board, witnesses, witnessed, actions, playStyle, pe) {

        this.board = board;
        this.actions = actions;
        this.witnesses = witnesses;
        this.witnessed = witnessed;
        this.playStyle = playStyle;
        this.pe = pe;

    }

    divideBigInt(numerator, denominator, dp) {

        const work = numerator * power10n[dp] / denominator;
    
        const result = Number(work) / power10[dp];
    
        return result;
    }

    countSolutions(board, notMines) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                continue;  // if the tile is a flag then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            let minesFound = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    minesFound++;
                } else if (adjTile.isCovered()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            // if a witness needs work (still has hidden adjacent tiles) or is broken then add it to the mix
            if (needsWork || minesFound > tile.getValue()) {
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        //console.log("tiles left = " + squaresLeft);
        //console.log("mines left = " + minesLeft);
        //console.log("Witnesses  = " + witnesses.length);
        //console.log("Witnessed  = " + witnessed.length);

        var solutionCounter = new SolutionCounter(board, witnesses, witnessed, squaresLeft, minesLeft);

        // let the solution counter know which tiles mustn't contain mines
        if (notMines != null) {
            for (let tile of notMines) {
                if (!solutionCounter.setMustBeEmpty(tile)) {
                    writeToConsole("Tile " + tile.asText() + " failed to set must be empty");
                }
            }
        }

        solutionCounter.process();

        return solutionCounter;

    }

    process() {

        // try the No flag efficiency strategy
        if (this.playStyle == PLAY_STYLE_NOFLAGS_EFFICIENCY) {
            return this.processNF(false);
        }

        if (this.playStyle != PLAY_STYLE_EFFICIENCY || this.actions.length == 0) {
            return this.actions;
        }

        let firstClear;
        let result = [];
        const chordLocations = [];

        // 1. look for tiles which are satisfied by known mines and work out the net benefit of placing the mines and then chording
        for (let tile of this.witnesses) {   // for each witness

            if (tile.getValue() == this.board.adjacentFoundMineCount(tile)) {

                // how many hidden tiles are next to the mine(s) we would have flagged, the more the better
                // this favours flags with many neighbours over flags buried against cleared tiles.
                const hiddenMineNeighbours = new Set();  
                for (let adjMine of this.board.getAdjacent(tile)) {

                    if (!adjMine.isSolverFoundBomb()) {
                        continue;
                    }
                    for (let adjTile of this.board.getAdjacent(adjMine)) {
                        if (!adjTile.isSolverFoundBomb() && adjTile.isCovered()) {
                            hiddenMineNeighbours.add(adjTile.index);
                        }
                    }                       
                }

                var benefit = this.board.adjacentCoveredCount(tile);
                var cost = tile.getValue() - this.board.adjacentFlagsPlaced(tile);
                if (tile.getValue() != 0) {  // if the witness isn't a zero then add the cost of chording - zero can only really happen in the analyser
                    cost++;
                }

                // either we have a net gain, or we introduce more flags at zero cost. more flags means more chance to get a cheaper chord later
                if (benefit >= cost) {
                    console.log("Chord " + tile.asText() + " has reward " + (benefit - cost) + " and tiles adjacent to new flags " + hiddenMineNeighbours.size);
                    chordLocations.push(new ChordLocation(tile, benefit, cost, hiddenMineNeighbours.size));
                }

            }
        }

        // sort the chord locations so the best one is at the top
        chordLocations.sort(function (a, b) {
            if (a.netBenefit == b.netBenefit) {  // if the benefits are the same return the one with the lowest cost (this means place less flags)
                //return a.cost - b.cost;
                return b.exposedTiles - a.exposedTiles;
            } else {
                return b.netBenefit - a.netBenefit;
            }
        });

        let bestChord = null;
        let witnessReward = 0;
        for (let cl of chordLocations) {

            if (cl.netBenefit > 0 || EfficiencyHelper.ALLOW_ZERO_NET_GAIN_CHORD && cl.netBenefit == 0 && cl.cost > 0) {
                bestChord = cl;
                witnessReward = cl.netBenefit;
            }

            break;
        }

        if (bestChord != null) {
            console.log("Chord " + bestChord.tile.asText() + " has best reward of " + bestChord.netBenefit);
        } else {
            console.log("No chord with net benefit > 0");
        }


        // 2. look for safe tiles which could become efficient if they have a certain value 
        //if (result.length == 0) {

            //if (this.actions.length < 2) {
            //    return this.actions;
            //}

            let bestAction = null;
            let highest = BigInt(0);

            const currSolnCount = this.countSolutions(this.board);
            if (witnessReward != 0) {
                highest = currSolnCount.finalSolutionsCount * BigInt(witnessReward);
            } else {
                highest = BigInt(0);
            }

            for (let act of this.actions) {

                if (act.action == ACTION_CLEAR) {

                    // this is the default move;
                    if (firstClear == null) {
                        firstClear = act;
                    }

                    const tile = this.board.getTileXY(act.x, act.y);

                    // find the best chord adjacent to this clear if there is one
                    let adjChord = null;
                    for (let cl of chordLocations) {
                        if (cl.netBenefit == 0 && !EfficiencyHelper.ALLOW_ZERO_NET_GAIN_PRE_CHORD) {
                            continue;
                        }

                        if (cl.tile.isAdjacent(tile)) {
                            // first adjacent chord, or better adj chord or cheaper adj chord 
                            if (adjChord == null || adjChord.netBenefit < cl.netBenefit || adjChord.netBenefit == cl.netBenefit && adjChord.cost > cl.cost || 
                                adjChord.netBenefit == cl.netBenefit && adjChord.cost == cl.cost && adjChord.exposedTiles < cl.exposedTiles) {
                                //adjBenefit = cl.netBenefit;
                                adjChord = cl;
                            }
                        }
                    }
                    if (adjChord == null) {
                        //console.log("(" + act.x + "," + act.y + ") has no adjacent chord with net benefit > 0");
                    } else {
                        console.log("(" + act.x + "," + act.y + ") has adjacent chord " + adjChord.tile.asText() + " with net benefit " + adjChord.netBenefit);
                     }

                    const adjMines = this.board.adjacentFoundMineCount(tile);
                    const adjFlags = this.board.adjacentFlagsPlaced(tile);
                    const hidden = this.board.adjacentCoveredCount(tile);   // hidden excludes unflagged but found mines

                    let chord;
                    if (adjMines != 0) {  // if the value we want isn't zero subtract the cost of chording
                        chord = 1;
                    } else {
                        chord = 0;
                    }

                     const reward = hidden - adjMines + adjFlags - chord;

                    //console.log("considering " + act.x + "," + act.y + " with value " + adjMines + " and reward " + reward + " ( H=" + hidden + " M=" + adjMines + " F=" + adjFlags + " Chord=" + chord + ")");

                    if (reward > witnessReward) {

                        tile.setValue(adjMines);
                        const counter = this.countSolutions(this.board);
                        tile.setCovered(true);

                        const prob = this.divideBigInt(counter.finalSolutionsCount, currSolnCount.finalSolutionsCount, 4);
                        const expected = prob * reward;

                        // set this information on the tile, so we can display it in the tooltip
                        tile.setValueProbability(adjMines, prob);

                        console.log("considering Clear (" + act.x + "," + act.y + ") with value " + adjMines + " and reward " + reward + " ( H=" + hidden + " M=" + adjMines + " F=" + adjFlags + " Chord=" + chord
                            + " Prob=" + prob + "), expected benefit " + expected);

                        // if we have found an 100% safe zero then just click it.
                        if (adjMines == 0 && prob == 1) {
                            console.log("(" + act.x + "," + act.y + ") is a certain zero no need for further analysis");
                            bestAction = act;
                            break;
                            //adjChord = null;
                            //highest = 0;
                        }

                        const clickChordNetBenefit = BigInt(reward) * counter.finalSolutionsCount; // expected benefit from clicking the tile then chording it

                        let current;
                        // if it is a chord/chord combo
                        if (adjChord != null) {
                            current = this.chordChordCombo(adjChord, tile, counter.finalSolutionsCount, currSolnCount.finalSolutionsCount);
                            if (current < clickChordNetBenefit) {  // if click chord is better then discard the adjacent chord
                                current = clickChordNetBenefit;
                                adjChord = null;
                            }

                        } else {  // or a clear/chord combo
                            current = clickChordNetBenefit;  // expected benefit == p*benefit
                        }

                        if (current > highest) {
                            //console.log("best " + act.x + "," + act.y);
                            highest = current;
                            if (adjChord != null) {  // if there is an adjacent chord then use this to clear the tile
                                bestChord = adjChord;
                                bestAction = null;
                            } else {
                                bestChord = null;
                                bestAction = act;
                            }
  
                        }
                    } else {
                        console.log("not considering (" + act.x + "," + act.y + ") with value " + adjMines + " and reward " + reward + " ( H=" + hidden + " M=" + adjMines + " F=" + adjFlags + " Chord=" + chord + ")");
                    }
                }

            }

            if (bestAction != null) {
                result = [bestAction];
            }

            if (bestChord != null) {
                result = []
                // add the required flags
                for (let adjTile of this.board.getAdjacent(bestChord.tile)) {
                    if (adjTile.isSolverFoundBomb() && !adjTile.isFlagged()) {
                        result.push(new Action(adjTile.getX(), adjTile.getY(), 0, ACTION_FLAG));
                    }
                }

                // Add the chord action
                result.push(new Action(bestChord.tile.getX(), bestChord.tile.getY(), 0, ACTION_CHORD))
            }
 

        //}

        if (result.length > 0) {
            return result;   // most efficient move

        } else {  // see if there are any safe tiles which are 3bv neutral
            //const neutral = this.processNF(true);
            //if (neutral.length > 0) {
            //    result.push(neutral[0]);
            //    return result;
            //}
        }


        if (firstClear != null) {
            return [firstClear];  // first clear when no efficient move
        } else {
            return [];  // nothing when no clears available
        }


    }

    // the ChordLocation of the tile to chord, the Tile to be chorded afterwards if the value comes up good, the number of solutions where this occurs
    // and the total number of solutions
    // this method works out the net benefit of this play
    chordChordCombo(chord1, chord2Tile, occurs, total) {

        const failedBenefit = chord1.netBenefit;
 
        const chord1Tile = chord1.tile;

        // now check each tile around the tile to be chorded 2nd and see how many mines to flag and tiles will be cleared
        //var alreadyCounted = 0;
        let needsFlag = 0;
        let clearable = 0;
        let chordClick = 0;
        for (let adjTile of this.board.getAdjacent(chord2Tile)) {

            if (adjTile.isSolverFoundBomb()) {
                chordClick = 1;
            }

            // if adjacent to chord1
            if (chord1Tile.isAdjacent(adjTile)) {
                //alreadyCounted++;
            } else if (adjTile.isSolverFoundBomb() && !adjTile.isFlagged()) {
                needsFlag++;
            } else if (!adjTile.isSolverFoundBomb() && adjTile.isCovered()) {
                clearable++;
            }
        }

        const secondBenefit = clearable - needsFlag - chordClick;  // tiles cleared - flags placed - the chord click (which isn't needed if a zero is expected)

        const score = BigInt(failedBenefit) * total + BigInt(secondBenefit) * occurs;

        const expected = failedBenefit + this.divideBigInt(occurs, total, 6) * secondBenefit;

        console.log("Chord " + chord1Tile.asText() + " followed by Chord " + chord2Tile.asText() + ": Chord 1: benefit " + chord1.netBenefit + ", Chord2: H=" + clearable + ", to F=" + needsFlag + ", Chord=" + chordClick
            + ", Benefit=" + secondBenefit + " ==> expected benefit " + expected);

        //var score = BigInt(failedBenefit) * total + BigInt(secondBenefit) * occurs;

        return score;

    }


    //
    // Below here is the logic for No-flag efficiency
    //
    processNF(SafeOnly) {

        const NFE_BLAST_PENALTY = 0.75;

        // the first clear in the actions list
        let firstClear = null;

        // clear the adjacent mine indicator
        for (let tile of this.board.tiles) {
            tile.adjacentMine = false;
        }

        const alreadyChecked = new Set(); // set of tiles we've already checked to see if they can be zero

        // set the adjacent mine indicator
        for (let tile of this.board.tiles) {
            if (tile.isSolverFoundBomb() || tile.probability == 0) {
                for (let adjTile of this.board.getAdjacent(tile)) {
                    if (!adjTile.isSolverFoundBomb() && adjTile.isCovered()) {
                        adjTile.adjacentMine = true;
                        adjTile.setValueProbability(0, 0);  // no chance of this tile being a zero

                        alreadyChecked.add(adjTile.index);

                    }
 
                }
            }
        }

        // find the current solution count
        const currSolnCount = this.countSolutions(this.board);

        let result = [];
        let zeroTile;
        let zeroTileScore;



        const onEdgeSet = new Set();
        for (let tile of this.witnessed) {
            onEdgeSet.add(tile.index);
        }

        // these are tiles adjacent to safe witnesses which aren't themselves safe
        const adjacentWitnessed = new Set();

        // do a more costly check for whether zero is possible, for those which haven't already be determined
        for (let tile of this.witnessed) {

            if (!alreadyChecked.has(tile.index) && !tile.isSolverFoundBomb() && !tile.probability == 0) { // already evaluated or a mine
                tile.setValue(0);
                const counter = this.countSolutions(this.board);
                tile.setCovered(true);

                const zeroProb = this.divideBigInt(counter.finalSolutionsCount, currSolnCount.finalSolutionsCount, 6);

                // set this information on the tile, so we can display it in the tooltip
                tile.setValueProbability(0, zeroProb);

                alreadyChecked.add(tile.index);

                if (counter.finalSolutionsCount == 0) {  // no solution where this tile is zero means there must always be an adjacent mine
                    tile.adjacentMine = true;
                } else if (counter.finalSolutionsCount == currSolnCount.finalSolutionsCount) {
                    console.log("Tile " + tile.asText() + " is a certain zero");
                    result.push(new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR));
                    break;
                } else {

                    const safety = this.pe.getProbability(tile);

                    const score = zeroProb - (1 - safety) * NFE_BLAST_PENALTY;

                    if (zeroTile == null || zeroTileScore < score) {
                        zeroTile = tile;
                        zeroTileScore = score;
                    }
 
                }
            }

            for (let adjTile of this.board.getAdjacent(tile)) {
                if (adjTile.isCovered() && !adjTile.isSolverFoundBomb() && adjTile.probability != 0 && !onEdgeSet.has(adjTile.index)) {
                    //console.log("Adding tile " + adjTile.asText() + " to extra tiles");
                    adjacentWitnessed.add(adjTile.index);
                } else {
                    //console.log("NOT Adding tile " + adjTile.asText() + " to extra tiles: On edge " + adjTile.onEdge);
                }
            }

        }

         // do a more costly check for whether zero is possible for actions not already considered, for those which haven't already be determined
        for (let act of this.actions) {

            const tile = this.board.getTileXY(act.x, act.y);

            if (act.action == ACTION_CLEAR && !alreadyChecked.has(tile.index) && !tile.isSolverFoundBomb() && !tile.probability == 0) { // already evaluated or a mine
                tile.setValue(0);
                const counter = this.countSolutions(this.board);
                tile.setCovered(true);

                const zeroProb = this.divideBigInt(counter.finalSolutionsCount, currSolnCount.finalSolutionsCount, 6);

                // set this information on the tile, so we can display it in the tooltip
                tile.setValueProbability(0, zeroProb);

                alreadyChecked.add(tile.index);

                if (counter.finalSolutionsCount == 0) {  // no solution where this tile is zero means there must always be an adjacent mine
                    tile.adjacentMine = true;
                } else if (counter.finalSolutionsCount == currSolnCount.finalSolutionsCount) {
                    console.log("Tile " + tile.asText() + " is a certain zero");
                    result.push(act);
                    break;
                } else {

                    const safety = this.pe.getProbability(tile);

                    const score = zeroProb - (1 - safety) * NFE_BLAST_PENALTY;

                    if (zeroTile == null || zeroTileScore < score) {
                        zeroTile = tile;
                        zeroTileScore = score;
                    }
                }
            }

            for (let adjTile of this.board.getAdjacent(tile)) {
                if (adjTile.isCovered() && !adjTile.isSolverFoundBomb() && adjTile.probability != 0 && !onEdgeSet.has(adjTile.index)) {
                    //console.log("Adding tile " + adjTile.asText() + " to extra tiles");
                    adjacentWitnessed.add(adjTile.index);
                } else {
                    //console.log("NOT Adding tile " + adjTile.asText() + " to extra tiles: On edge " + adjTile.onEdge);
                }
            }

        }

        console.log("Extra tiles to check " + adjacentWitnessed.size);

        // we have found a certain zero
        if (result.length > 0) {
            return result;
        }

        let offEdgeSafety;
        if (this.pe == null) {
            offEdgeSafety = 1;
        } else {
            offEdgeSafety = this.pe.offEdgeProbability;
        }

        // see if adjacent tiles can be zero or not
        for (let index of adjacentWitnessed) {
            const tile = this.board.getTile(index);

            tile.setValue(0);
            const counter = this.countSolutions(this.board);
            tile.setCovered(true);

            const prob = this.divideBigInt(counter.finalSolutionsCount, currSolnCount.finalSolutionsCount, 6);

            // set this information on the tile, so we can display it in the tooltip
            tile.setValueProbability(0, prob);

            if (counter.finalSolutionsCount == 0) {  // no solution where this tile is zero means there must always be an adjacent mine
                tile.adjacentMine = true;
            } else if (counter.finalSolutionsCount == currSolnCount.finalSolutionsCount) {
                console.log("Tile " + tile.asText() + " is a certain zero");
                result.push(new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR));
                break;
            } else {

                const score = prob - (1 - offEdgeSafety) * NFE_BLAST_PENALTY;

                if (zeroTile == null || zeroTileScore < score) {
                    zeroTile = tile;
                    zeroTileScore = score;
                }
            }

        }

        // we have found a certain zero
        if (result.length > 0) {
            return result;
        }


        let maxAllNotZeroProbability;
        let bestAllNotZeroAction;
        // see if any of the safe tiles are also surrounded by all non-zero tiles
        for (let act of this.actions) {

            if (act.action == ACTION_CLEAR) {

                // this is the default move;
                if (firstClear == null) {
                    firstClear = act;
                }

                let valid = true;
                let allNotZeroProbability = 1;
                for (let adjTile of this.board.getAdjacent(act)) {
                    if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                        valid = valid && adjTile.adjacentMine;
                        allNotZeroProbability = allNotZeroProbability * (1 - adjTile.efficiencyProbability);
                    }
                }

                if (bestAllNotZeroAction == null || maxAllNotZeroProbability < allNotZeroProbability) {
                    bestAllNotZeroAction = act;
                    maxAllNotZeroProbability = allNotZeroProbability;
                }

                if (valid) {
                    console.log("Tile " + act.asText() + " is 3BV safe because it can't be next to a zero");
                    result.push(act);
                }
            }
 
        }

        if (result.length > 0 || SafeOnly) {
            return result;
        }


        if (bestAllNotZeroAction != null) {
            console.log("Tile " + bestAllNotZeroAction.asText() + " has no adjacent zero approx " + maxAllNotZeroProbability);
        }
        if (zeroTile != null) {
            console.log("Tile " + zeroTile.asText() + " has best zero chance score " + zeroTileScore);
        }

        if (zeroTile != null) {

            let prob;
            if (this.pe == null) {
                prob = 1;
            } else {
                prob = this.pe.getProbability(zeroTile);
            }

            if (bestAllNotZeroAction != null) {
                //const zeroTileProb = this.divideBigInt(zeroTileCount, currSolnCount.finalSolutionsCount, 6);
                if (maxAllNotZeroProbability > zeroTileScore && zeroTileScore < 0.0) {
                    result.push(bestAllNotZeroAction);
                } else {
                    result.push(new Action(zeroTile.getX(), zeroTile.getY(), prob, ACTION_CLEAR));
                }
            } else {
                result.push(new Action(zeroTile.getX(), zeroTile.getY(), prob, ACTION_CLEAR));
            }
        } else {
            if (bestAllNotZeroAction != null) {
                result.push(bestAllNotZeroAction);
            }
        }

        if (result.length > 0) {
            return result;
        }

        if (firstClear != null) {
            return [firstClear];  // first clear when no efficient move
        } else {
            return [];  // nothing when no clears available
        }


    }

}

// information about the boxes surrounding a dead candidate
class ChordLocation {

    constructor(tile, benefit, cost, exposedTiles) {

        this.tile = tile;
        this.benefit = benefit;
        this.cost = cost;
        this.netBenefit = benefit - cost;
        this.exposedTiles = exposedTiles;

    }

}

class FiftyFiftyHelper {

	// ways to place mines in a 2x2 box
	static PATTERNS = [
		[true, true, true, true],   // four mines
		[true, true, true, false], [true, false, true, true], [false, true, true, true], [true, true, false, true],   // 3 mines
		[true, false, true, false], [false, true, false, true], [true, true, false, false], [false, false, true, true],   // 2 mines
		[false, true, false, false], [false, false, false, true], [true, false, false, false], [false, false, true, false]  // 1 mine   
	];


    constructor(board, minesFound, options, deadTiles, witnessedTiles, minesLeft) {

        this.board = board;
        this.options = options;
        this.minesFound = minesFound;  // this is a list of tiles which the probability engine knows are mines
		this.deadTiles = deadTiles;
		this.witnessedTiles = witnessedTiles;
		this.minesLeft = minesLeft;

    }

	countSolutions(board, notMines) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                continue;  // if the tile is a flag then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            let minesFound = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    minesFound++;
                } else if (adjTile.isCovered()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            // if a witness needs work (still has hidden adjacent tiles) or is broken then add it to the mix
            if (needsWork || minesFound > tile.getValue()) {
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        //console.log("tiles left = " + squaresLeft);
        //console.log("mines left = " + minesLeft);
        //console.log("Witnesses  = " + witnesses.length);
        //console.log("Witnessed  = " + witnessed.length);

        var solutionCounter = new SolutionCounter(board, witnesses, witnessed, squaresLeft, minesLeft);

        // let the solution counter know which tiles mustn't contain mines
        if (notMines != null) {
            for (let tile of notMines) {
                if (!solutionCounter.setMustBeEmpty(tile)) {
                    writeToConsole("Tile " + tile.asText() + " failed to set must be empty");
                }
            }
        }

        solutionCounter.process();

        return solutionCounter;

    }

    // this process looks for positions which are either 50/50 guesses or safe.  In which case they should be guessed as soon as possible
    process() {

        const startTime = Date.now();

        // place all the mines found by the probability engine
        for (let mine of this.minesFound) {
            mine.setFoundBomb();
        }

		for (let i = 0; i < this.board.width - 1; i++) {
			for (let j = 0; j < this.board.height; j++) {

                const tile1 = this.board.getTileXY(i, j);
				if (!tile1.isCovered() || tile1.isSolverFoundBomb()) {  // cleared or a known mine
                    continue;
                }

                const tile2 = this.board.getTileXY(i + 1, j);
				if (!tile2.isCovered() || tile2.isSolverFoundBomb()) {  // cleared or a known mine
                    continue;
                }

                // if information can come from any of the 6 tiles immediately right and left then can't be a 50-50
				if (this.isPotentialInfo(i - 1, j - 1) || this.isPotentialInfo(i - 1, j) || this.isPotentialInfo(i - 1, j + 1)
					|| this.isPotentialInfo(i + 2, j - 1) || this.isPotentialInfo(i + 2, j) || this.isPotentialInfo(i + 2, j + 1)) {
					continue;  // this skips the rest of the logic below this in the for-loop 
				}

                // is both hidden tiles being mines a valid option?
                tile1.setFoundBomb();
                tile2.setFoundBomb();
                var counter = this.countSolutions(this.board, null);
                tile1.unsetFoundBomb();
                tile2.unsetFoundBomb();

                if (counter.finalSolutionsCount != 0) {
                    this.writeToConsole(tile1.asText() + " and " + tile2.asText() + " can support 2 mines");
                } else {
                    this.writeToConsole(tile1.asText() + " and " + tile2.asText() + " can not support 2 mines, we should guess here immediately");
                    return tile1;
                 }

			}
		} 

        for (let i = 0; i < this.board.width; i++) {
            for (let j = 0; j < this.board.height - 1; j++) {

                const tile1 = this.board.getTileXY(i, j);
				if (!tile1.isCovered() || tile1.isSolverFoundBomb()) {  // cleared or a known mine
                    continue;
                }

                const tile2 = this.board.getTileXY(i, j + 1);
				if (!tile2.isCovered() || tile2.isSolverFoundBomb()) {  // cleared or a known mine
                    continue;
                }

                // if information can come from any of the 6 tiles immediately above and below then can't be a 50-50
                if (this.isPotentialInfo(i - 1, j - 1) || this.isPotentialInfo(i, j - 1) || this.isPotentialInfo(i + 1, j - 1)
                    || this.isPotentialInfo(i - 1, j + 2) || this.isPotentialInfo(i, j + 2) || this.isPotentialInfo(i + 1, j + 2)) {
                    continue;  // this skips the rest of the logic below this in the for-loop 
                }

                // is both hidden tiles being mines a valid option?
                tile1.setFoundBomb();
                tile2.setFoundBomb();
                var counter = this.countSolutions(this.board, null);
                tile1.unsetFoundBomb();
                tile2.unsetFoundBomb();

                if (counter.finalSolutionsCount != 0) {
                    this.writeToConsole(tile1.asText() + " and " + tile2.asText() + " can support 2 mines");
                } else {
                    this.writeToConsole(tile1.asText() + " and " + tile2.asText() + " can not support 2 mines, we should guess here immediately");
                    return tile1;
                }

            }
        } 

		// box 2x2
		const tiles = Array(4);

		//const mines = [];
		//const noMines = [];
		for (let i = 0; i < this.board.width - 1; i++) {
			for (let j = 0; j < this.board.height - 1; j++) {

				// need 4 hidden tiles
				tiles[0] = this.board.getTileXY(i, j);
				if (!tiles[0].isCovered() || tiles[0].isSolverFoundBomb()) {
					continue;
				}

				tiles[1] = this.board.getTileXY(i + 1, j);
				if (!tiles[1].isCovered() || tiles[1].isSolverFoundBomb()) {
					continue;
				}

				tiles[2] = this.board.getTileXY(i, j + 1);
				if (!tiles[2].isCovered() || tiles[2].isSolverFoundBomb()) {
					continue;
				}

				tiles[3] = this.board.getTileXY(i + 1, j + 1);
				if (!tiles[3].isCovered() || tiles[3].isSolverFoundBomb()) {
					continue;
				}

				// need the corners to be flags
				if (this.isPotentialInfo(i - 1, j - 1) || this.isPotentialInfo(i + 2, j - 1) || this.isPotentialInfo(i - 1, j + 2) || this.isPotentialInfo(i + 2, j + 2)) {
					continue;  // this skips the rest of the logic below this in the for-loop 
				}

				this.writeToConsole(tiles[0].asText() + " " + tiles[1].asText() + " " + tiles[2].asText() + " " + tiles[3].asText() + " is candidate box 50/50");

				// keep track of which tiles are risky - once all 4 are then not a pseudo-50/50
				let riskyTiles = 0;
				const risky = Array(4).fill(false);

				// check each tile is in the web and that at least one is living
				let okay = true;
				let allDead = true;
				for (let l = 0; l < 4; l++) {
					if (!this.isDead(tiles[l])) {
						allDead = false;
					} else {
						riskyTiles++;
						risky[l] = true;  // since we'll never select a dead tile, consider them risky
					}

					if (!this.isWitnessed(tiles[l])) {
						this.writeToConsole(tiles[l].asText() + " has no witnesses");
						okay = false;
						break;
					}
				}
				if (!okay) {
					continue;
				}
				if (allDead) {
					this.writeToConsole("All tiles in the candidate are dead");
					continue
				}

				let start;
				if (this.minesLeft > 3) {
					start = 0;
				} else if (this.minesLeft == 3) {
					start = 1;
				} else if (this.minesLeft == 2) {
					start = 5;
				} else {
					start = 9;
				}

				for (let k = start; k < FiftyFiftyHelper.PATTERNS.length; k++) {

					const mines = [];
					const noMines = [];

					var run = false;
					// allocate each position as a mine or noMine
					for (let l = 0; l < 4; l++) {
						if (FiftyFiftyHelper.PATTERNS[k][l]) {
							mines.push(tiles[l]);
							if (!risky[l]) {
								run = true;
							}
						} else {
							noMines.push(tiles[l]);
						}
					}

					// only run if this pattern can discover something we don't already know
					if (!run) {
						this.writeToConsole("Pattern " + k + " skipped");
						continue;
					}

					// place the mines
					for (let tile of mines) {
						tile.setFoundBomb();
					}

					// see if the position is valid
					const counter = this.countSolutions(this.board, noMines);

					// remove the mines
					for (let tile of mines) {
						tile.unsetFoundBomb();
					}

					// if it is then mark each mine tile as risky
					if (counter.finalSolutionsCount != 0) {
						this.writeToConsole("Pattern " + k + " is valid");
						for (let l = 0; l < 4; l++) {
							if (FiftyFiftyHelper.PATTERNS[k][l]) {
								if (!risky[l]) {
									risky[l] = true;
									riskyTiles++;
								}
							}
						}
						if (riskyTiles == 4) {
							break;
						}
					} else {
						this.writeToConsole("Pattern " + k + " is not valid");
					}
				}

				// if not all 4 tiles are risky then send back one which isn't
				if (riskyTiles != 4) {
					for (let l = 0; l < 4; l++) {
						// if not risky and not dead then select it
						if (!risky[l]) {
							this.writeToConsole(tiles[0].asText() + " " + tiles[1].asText() + " " + tiles[2].asText() + " " + tiles[3].asText() + " is pseudo 50/50 - " + tiles[l].asText() + " is not risky");
							return tiles[l];
						}

					}
				}
			}
		}                        

        this.duration = Date.now() - startTime;

        // remove all the mines found by the probability engine - if we don't do this it upsets the brute force deep analysis processing
        for (var mine of this.minesFound) {
            mine.unsetFoundBomb();
        }

        this.writeToConsole("5050 checker took " + this.duration + " milliseconds");

        return null;

	}

    // returns whether there information to be had at this location; i.e. on the board and either unrevealed or revealed
    isPotentialInfo(x, y) {

        if (x < 0 || x >= this.board.width || y < 0 || y >= this.board.height) {
            return false;
        }

        if (this.board.getTileXY(x, y).isSolverFoundBomb()) {
            return false;
        } else {
            return true;
        }

    }

	isDead(tile) {

		//  is the tile dead
		for (let k = 0; k < this.deadTiles.length; k++) {
			if (this.deadTiles[k].isEqual(tile)) {
				return true;
			}
		}

		return false;

    }

	isWitnessed(tile) {

		//  is the tile witnessed
		for (let k = 0; k < this.witnessedTiles.length; k++) {
			if (this.witnessedTiles[k].isEqual(tile)) {
				return true;
			}
		}

		return false;

	}

    writeToConsole(text, always) {

        if (always == null) {
            always = false;
        }

        if (this.options.verbose || always) {
            console.log(text);
        }

    }

}

class LongTermRiskHelper {

	constructor(board, pe, minesLeft, options)  {

		this.board = board;
		//this.wholeEdge = wholeEdge;
		this.currentPe = pe;
		this.minesLeft = minesLeft
		this.options = options;

		this.pseudo = null;

		this.influence5050s = new Array(this.board.width * this.board.height);
		this.influenceEnablers = new Array(this.board.width * this.board.height);

		Object.seal(this) // prevent new properties being created

	}

	/**
	 * Scan whole board looking for tiles heavily influenced by 50/50s
	 */
	findInfluence() {

		//TODO place mines found by the probability engine

		this.checkFor2Tile5050();

		this.checkForBox5050();

		if (this.pseudo != null) {
			this.writeToConsole("Tile " + this.pseudo.asText() + " is a 50/50, or safe");
		}

		//TODO remove mines found by the probability engine

		return this.pseudo;

	}

	/**
	 * Get the 50/50 influence for a particular tile
	 */
	findTileInfluence(tile) {
		
		let influence = BigInt(0);
		
		// 2-tile 50/50
		const tile1 = this.board.getTileXY(tile.getX() - 1, tile.getY());

		influence = this.addNotNull(influence, this.getHorizontal(tile, 4));
		influence = this.addNotNull(influence, this.getHorizontal(tile1, 4));

		const tile2 = this.board.getTileXY(tile.getX(), tile.getY() - 1);
		influence = this.addNotNull(influence, this.getVertical(tile, 4));
		influence = this.addNotNull(influence, this.getVertical(tile2, 4));

		// 4-tile 50/50
		let influence4 = BigInt(0);
		const tile3 = this.board.getTileXY(tile.getX() - 1, tile.getY() - 1);
		influence4 = this.maxNotNull(influence4, this.getBoxInfluence(tile, 5));
		influence4 = this.maxNotNull(influence4, this.getBoxInfluence(tile1, 5));
		influence4 = this.maxNotNull(influence4, this.getBoxInfluence(tile2, 5));
		influence4 = this.maxNotNull(influence4, this.getBoxInfluence(tile3, 5));

		if (influence4 > 0) {
			this.writeToConsole("Tile " + tile.asText() + " best 4-tile 50/50 has tally " + influence4);
        }

		influence = influence + influence4;

		// enablers also get influence, so consider that as well as the 50/50
		if (this.influenceEnablers[tile.index] != null) {
			influence = influence + this.influenceEnablers[tile.index];
		}
		
		let maxInfluence;
		const box = this.currentPe.getBox(tile);
		if (box == null) {
			maxInfluence = this.currentPe.offEdgeMineTally;
		} else {
			maxInfluence = box.mineTally;
		}

		// 50/50 influence P(50/50)/2 can't be larger than P(mine) or P(safe)
		const other = this.currentPe.finalSolutionsCount - maxInfluence;

		maxInfluence = this.bigIntMin(maxInfluence, other);

		influence = this.bigIntMin(influence, maxInfluence);

		return influence;

	}
	
	checkFor2Tile5050() {
		
		const maxMissingMines = 2;

		this.writeToConsole("Checking for 2-tile 50/50 influence");
    	
		// horizontal 2x1
		for (let i = 0; i < this.board.width - 1; i++) {
			for (let j = 0; j < this.board.height; j++) {

				const tile1 = this.board.getTileXY(i, j);
				const tile2 = this.board.getTileXY(i + 1, j);
				
				const result = this.getHorizontal(tile1, maxMissingMines, this.minesLeft);

				if (result != null) {
					let influenceTally = this.addNotNull(BigInt(0), result);
					//const influence = this.divideBigInt(influenceTally, this.currentPe.finalSolutionsCount, 4); 
					//this.writeToConsole("Tile " + tile1.asText() + " and " + tile2.asText() + " have horiontal 2-tile 50/50 influence " + influence);

					this.addInfluence(influenceTally, result.enablers, [tile1, tile2]);
					if (this.pseudo != null) {  // if we've found a pseudo then we can stop here
						return;
					}
				}



			}
		}

		// vertical 2x1
		for (let i = 0; i < this.board.width; i++) {
			for (let j = 0; j < this.board.height - 1; j++) {

				const tile1 = this.board.getTileXY(i, j);
				const tile2 = this.board.getTileXY(i, j + 1);
				
				const result = this.getVertical(tile1, maxMissingMines, this.minesLeft);

				if (result != null) {
					
					let influenceTally = this.addNotNull(BigInt(0), result);
					//const influence = this.divideBigInt(influenceTally, this.currentPe.finalSolutionsCount, 4); 
					//this.writeToConsole("Tile " + tile1.asText() + " and " + tile2.asText() + " have vertical 2-tile 50/50 influence " + influence);

					this.addInfluence(influenceTally, result.enablers, [tile1, tile2]);
					if (this.pseudo != null) {  // if we've found a pseudo then we can stop here
						return;
					}
				}

			}
		}
	}

	countSolutions(board, notMines) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                continue;  // if the tile is a flag then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            let minesFound = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    minesFound++;
                } else if (adjTile.isCovered()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            // if a witness needs work (still has hidden adjacent tiles) or is broken then add it to the mix
            if (needsWork || minesFound > tile.getValue()) {
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        //console.log("tiles left = " + squaresLeft);
        //console.log("mines left = " + minesLeft);
        //console.log("Witnesses  = " + witnesses.length);
        //console.log("Witnessed  = " + witnessed.length);

        var solutionCounter = new SolutionCounter(board, witnesses, witnessed, squaresLeft, minesLeft);

        // let the solution counter know which tiles mustn't contain mines
        if (notMines != null) {
            for (let tile of notMines) {
                if (!solutionCounter.setMustBeEmpty(tile)) {
                    writeToConsole("Tile " + tile.asText() + " failed to set must be empty");
                }
            }
        }

        solutionCounter.process();

        return solutionCounter;

    }

	getHorizontal(subject, maxMissingMines) {

		if (subject == null) {
			return null;
        }

		const i = subject.x;
		const j = subject.y;

		if (i < 0 || i + 1 >= this.board.width) {
			return null;
		}

		// need 2 hidden tiles
		if (!this.isHidden(i, j) || !this.isHidden(i + 1, j)) {
			return null;
		}

		const missingMines = this.getMissingMines([this.board.getTileXY(i - 1, j - 1), this.board.getTileXY(i - 1, j), this.board.getTileXY(i - 1, j + 1),
			this.board.getTileXY(i + 2, j - 1), this.board.getTileXY(i + 2, j), this.board.getTileXY(i + 2, j + 1)]);

		// only consider possible 50/50s with less than 3 missing mines or requires more mines then are left in the game (plus 1 to allow for the extra mine in the 50/50)
		if (missingMines == null || missingMines.length + 1 > maxMissingMines || missingMines.length + 1 > this.minesLeft) {
			return null;
		}
		
		const tile1 = subject;
		const tile2 = this.board.getTileXY(i + 1, j);

		//this.writeToConsole("Evaluating candidate 50/50 - " + tile1.asText() + " " + tile2.asText());

		// add the missing Mines and the mine required to form the 50/50
		//missingMines.push(tile1);

		const mines = [...missingMines, tile1];
		const notMines = [tile2];

		// place the mines
		for (let tile of mines) {
			tile.setFoundBomb();
		}

		// see if the position is valid
		const counter = this.countSolutions(this.board, notMines);

		// remove the mines
		for (let tile of mines) {
			tile.unsetFoundBomb();
		}

		this.writeToConsole("Candidate 50/50 - " + tile1.asText() + " " + tile2.asText() + " has tally " + counter.finalSolutionsCount);
		

		return new LTResult(counter.finalSolutionsCount, missingMines);

	}
	
	getVertical(subject, maxMissingMines) {

		if (subject == null) {
			return null;
		}

		const i = subject.getX();
		const j = subject.getY();

		if (j < 0 || j + 1 >= this.board.height) {
			return null;
		}

		// need 2 hidden tiles
		if (!this.isHidden(i, j) || !this.isHidden(i, j + 1)) {
			return null;
		}

		const missingMines = this.getMissingMines([this.board.getTileXY(i - 1, j - 1), this.board.getTileXY(i, j - 1), this.board.getTileXY(i + 1, j - 1),
			this.board.getTileXY(i - 1, j + 2), this.board.getTileXY(i, j + 2), this.board.getTileXY(i + 1, j + 2)]);

		// only consider possible 50/50s with less than 3 missing mines or requires more mines then are left in the game (plus 1 to allow for the extra mine in the 50/50)
		if (missingMines == null || missingMines.length + 1 > maxMissingMines || missingMines.length + 1 > this.minesLeft) {
			return null;
		}
		
		const tile1 = this.board.getTileXY(i, j);
		const tile2 = this.board.getTileXY(i, j + 1);

		//this.writeToConsole("Evaluating candidate 50/50 - " + tile1.asText() + " " + tile2.asText());

		// add the missing Mines and the mine required to form the 50/50
		//missingMines.push(tile1);

		const mines = [...missingMines, tile1];
		const notMines = [tile2];

		// place the mines
		for (let tile of mines) {
			tile.setFoundBomb();
		}

		// see if the position is valid
		const counter = this.countSolutions(this.board, notMines);

		// remove the mines
		for (let tile of mines) {
			tile.unsetFoundBomb();
		}

		this.writeToConsole("Candidate 50/50 - " + tile1.asText() + " " + tile2.asText() + " has tally " + counter.finalSolutionsCount);

		return new LTResult(counter.finalSolutionsCount, missingMines);

	}

	divideBigInt(numerator, denominator, dp) {

		const work = numerator * power10n[dp] / denominator;
	
		const result = Number(work) / power10[dp];
	
		return result;
	}

	checkForBox5050() {
		
		const maxMissingMines = 2;
		
		this.writeToConsole("Checking for 4-tile 50/50 influence");

		// box 2x2 
		for (let i = 0; i < this.board.width - 1; i++) {
			for (let j = 0; j < this.board.height - 1; j++) {

				const tile1 = this.board.getTileXY(i, j);
				const tile2 = this.board.getTileXY(i, j + 1);
				const tile3 = this.board.getTileXY(i + 1, j);
				const tile4 = this.board.getTileXY(i + 1, j + 1);
				
				const result = this.getBoxInfluence(tile1, maxMissingMines);

				if (result != null) {
					
					const influenceTally = this.addNotNull(BigInt(0), result);
					
					const influence = this.divideBigInt(influenceTally, this.currentPe.finalSolutionsCount, 4); 
					//this.writeToConsole("Tile " + tile1.asText() + " " + tile2.asText() + " " + tile3.asText() + " " + tile4.asText() + " have box 4-tile 50/50 influence " + influence);

					this.addInfluence(influenceTally, result.enablers, [tile1, tile2, tile3, tile4]);
					if (this.pseudo != null) {  // if we've found a pseudo then we can stop here
						return;
					}
				}

			}
		}

	}
	
	getBoxInfluence(subject, maxMissingMines) {

		if (subject == null) {
			return null;
		}

		const i = subject.getX();
		const j = subject.getY();

		if (j < 0 || j + 1 >= this.board.height || i < 0 || i + 1 >= this.board.width) {
			return null;
		}

		// need 4 hidden tiles
		if (!this.isHidden(i, j) || !this.isHidden(i, j + 1) || !this.isHidden(i + 1, j) || !this.isHidden(i + 1, j + 1)) {
			return null;
		}

		const missingMines = this.getMissingMines([this.board.getTileXY(i - 1, j - 1), this.board.getTileXY(i + 2, j - 1), this.board.getTileXY(i - 1, j + 2), this.board.getTileXY(i + 2, j + 2)]);

		// only consider possible 50/50s with less than 3 missing mines or requires more mines then are left in the game (plus 1 to allow for the extra mine in the 50/50)
		if (missingMines == null || missingMines.length + 2 > maxMissingMines || missingMines.length + 2 > this.minesLeft) {
			return null;
		}
		
		const tile1 = this.board.getTileXY(i, j);
		const tile2 = this.board.getTileXY(i, j + 1);
		const tile3 = this.board.getTileXY(i + 1, j);
		const tile4 = this.board.getTileXY(i + 1, j + 1);

		//this.writeToConsole("Evaluating candidate 50/50 - " + tile1.asText() + " " + tile2.asText() + " " + tile3.asText() + " " + tile4.asText());

		// add the missing Mines and the mine required to form the 50/50
		//missingMines.push(tile1);
		//missingMines.push(tile4);

		const mines = [...missingMines, tile1, tile4];
		const notMines = [tile2, tile3];

		// place the mines
		for (let tile of mines) {
			tile.setFoundBomb();
		}

		// see if the position is valid
		const counter = this.countSolutions(this.board, notMines);

		this.writeToConsole("Candidate 50/50 - " + tile1.asText() + " " + tile2.asText() + " " + tile3.asText() + " " + tile4.asText() + " tally " + counter.finalSolutionsCount);
		
		// remove the mines
		for (let tile of mines) {
			tile.unsetFoundBomb();
		}

		return new LTResult(counter.finalSolutionsCount, missingMines);

	}
	
	addNotNull(influence, result) {

		if (result == null) {
			return influence;
		} else {
			return influence + result.influence;
		}

	}

	maxNotNull(influence, result) {

		if (result == null) {
			return influence;
		} else {
			return this.bigIntMax(influence, result.influence);
		}

	}

	addInfluence(influence, enablers, tiles) {

		const pseudos = [];

		// the tiles which enable a 50/50 but aren't in it also get an influence
		if (enablers != null) {
			for (let loc of enablers) {

				// store the influence
				if (this.influenceEnablers[loc.index] == null) {
					this.influenceEnablers[loc.index] = influence;
				} else {
					this.influenceEnablers[loc.index] = this.influenceEnablers[loc.index] + influence;
				}
				//this.writeToConsole("Enabler " + loc.asText() + " has influence " + this.influences[loc.index]);
			}
		}

		for (let loc of tiles) {
			
			const b = this.currentPe.getBox(loc);
			let mineTally;
			if (b == null) {
				mineTally = this.currentPe.offEdgeMineTally;
			} else {
				mineTally = b.mineTally;
			}
			// If the mine influence covers the whole of the mine tally then it is a pseudo-5050
			if (influence == mineTally && this.pseudo == null) {
				if (!this.currentPe.isDead(loc)) {  // don't accept dead tiles
					pseudos.push(loc);
				}
			}

			// store the influence
			if (this.influence5050s[loc.index] == null) {
				this.influence5050s[loc.index] = influence;
			} else {
				//influences[loc.x][loc.y] = influences[loc.x][loc.y].max(influence);
				this.influence5050s[loc.index] = this.influence5050s[loc.index] + influence;
			}
			//this.writeToConsole("Interior " + loc.asText() + " has influence " + this.influences[loc.index]);
		}

		if (pseudos.length == 3) {
			this.pickPseudo(pseudos);
		} else if (pseudos.length != 0) {
			this.pseudo = pseudos[0];
        }

	}

	pickPseudo(locations) {

		let maxX = 0;
		let maxY = 0;

		for (let loc of locations) {
			maxX = Math.max(maxX, loc.getX());
			maxY = Math.max(maxY, loc.getY());
		}

		const maxX1 = maxX - 1;
		const maxY1 = maxY - 1;

		let found = 0;
		for (let loc of locations) {
			if (loc.getX() == maxX && loc.getY() == maxY || loc.getX() == maxX1 && loc.getY() == maxY1) {
				found++;
			}
		}

		// if the 2 diagonals exist then choose the pseudo from those, other wise choose the pseudo from the other diagonal
		if (found == 2) {
			this.pseudo = this.board.getTileXY(maxX, maxY);
		} else {
			this.pseudo = this.board.getTileXY(maxX1, maxY);
		}

	}


	/**
	 * Get how many solutions have common 50/50s at this location
	 */
	/*
	get5050Influence(loc) {

		if (influences[loc.index] == null) {
			return BigInt(0);
		} else {
			return influences[loc.index];
		}

	}
	*/

	/**
	 * Return all the locations with 50/50 influence
	 */
	getInfluencedTiles(threshold) {

		const top = BigInt(Math.floor(threshold * 10000));
		const bot = BigInt(10000);

		const cutoffTally = this.currentPe.finalSolutionsCount * top / bot;

		const result = [];

		for (let tile of this.board.tiles) {

			let influence = BigInt(0);

			if (this.influence5050s[tile.index] != null) {
				influence = influence + this.influence5050s[tile.index];
            }
			if (this.influenceEnablers[tile.index] != null) {
				influence = influence + this.influenceEnablers[tile.index];
			}

			if (influence != 0) {	  // if we are influenced by 50/50s

				if (!this.currentPe.isDead(tile)) {  // and not dead

					const b = this.currentPe.getBox(tile);
					let mineTally;
					if (b == null) {
						mineTally = this.currentPe.offEdgeMineTally;
					} else {
						mineTally = b.mineTally;
					}

					const safetyTally = this.currentPe.finalSolutionsCount - mineTally + influence;

					if (safetyTally > cutoffTally) {
						//this.writeToConsole("Tile " + tile.asText() + " has mine tally " + mineTally + " influence " + this.influences[tile.index]);
						//this.writeToConsole("Tile " + tile.asText() + " has  modified tally  " + safetyTally + " cutoff " + cutoffTally);
						result.push(tile);
					}

				}
			}
		}

		return result;
	}

	// given a list of tiles return those which are on the board but not a mine
	// if any of the tiles are revealed then return null
	getMissingMines(tiles) {

		const result = [];

		for (let loc of tiles) {

			if (loc == null) {
				continue;
            }

			// if out of range don't return the location
			if (loc.getX() >= this.board.width || loc.getX() < 0 || loc.getY() < 0 || loc.getY() >= this.board.getHeight) {
				continue;
			}

			// if the tile is revealed then we can't form a 50/50 here
			if (!loc.isCovered()) {
				return null;
			}

			// if the location is already a mine then don't return the location
			if (loc.isSolverFoundBomb()) {
				continue;
			}

			result.push(loc);
		}

		return result;
	}



	// not a certain mine or revealed
	isHidden(x, y) {

		const tile = this.board.getTileXY(x, y);

		if (tile.isSolverFoundBomb()) {
			return false;
		}

		if (!tile.isCovered()) {
			return false;
		}

		return true;

	}

	bigIntMin(a, b) {
		if (a < b) {
			return a;
		} else {
			return b;
        }
    }

	bigIntMax(a, b) {
		if (a > b) {
			return a;
		} else {
			return b;
        }
    }

	writeToConsole(text, always) {

		if (always == null) {
			always = false;
		}

		if (this.options.verbose || always) {
			console.log(text);
		}

	}
}

class LTResult {
	constructor(influence, enablers) {
		this.influence = influence;
		this.enablers = enablers;

		Object.seal(this) // prevent new properties being created
	}
}

class ProbabilityEngine {

    static SMALL_COMBINATIONS = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1], [1, 5, 10, 10, 5, 1], [1, 6, 15, 20, 15, 6, 1], [1, 7, 21, 35, 35, 21, 7, 1], [1, 8, 28, 56, 70, 56, 28, 8, 1]];

	constructor(board, allWitnesses, allWitnessed, squaresLeft, minesLeft, options) {

        this.BINOMIAL = new Binomial(50000, 200);

        this.board = board;
        this.options = options;
        this.playStyle = options.playStyle;
        this.verbose = options.verbose;

		this.witnessed = allWitnessed;

        this.duration = 0;

        this.prunedWitnesses = [];  // a subset of allWitnesses with equivalent witnesses removed

        // constraints in the game
        this.minesLeft = minesLeft;
        this.tilesLeft = squaresLeft;
        this.TilesOffEdge = squaresLeft - allWitnessed.length;   // squares left off the edge and unrevealed
        this.minTotalMines = minesLeft - this.TilesOffEdge;   // //we can't use so few mines that we can't fit the remainder elsewhere on the board
        this.maxTotalMines = minesLeft;

        this.boxes = [];
        this.boxWitnesses = [];
        this.mask = [];

        // list of 'DeadCandidate' which are potentially dead
        this.deadCandidates = [];
        this.deadTiles = [];
        this.lonelyTiles = [];  // tiles with no empty space around them

        this.emptyBoxes = [];  // boxes which never contain mines - i.e. the set of safe tiles by Box

        this.boxProb = [];  // the probabilities end up here
		this.workingProbs = []; 
        this.heldProbs = [];
        this.bestProbability = 0;  // best probability of being safe
        this.offEdgeProbability = 0;
        this.offEdgeMineTally = 0;
        this.bestOnEdgeProbability = BigInt(0);
        this.finalSolutionsCount = BigInt(0);

        this.bestLivingProbability = 0;

        // details about independent witnesses
        this.independentWitnesses = [];
        this.dependentWitnesses = [];
        this.independentMines = 0;
        this.independentIterations = BigInt(1);
        this.remainingSquares = 0;

        this.clearCount = 0;
        this.localClears = [];
        this.fullAnalysis = false;  // unless we are playing efficiency mode we'll stop after we find some safe tiles

        this.minesFound = [];  // discovered mines are stored in here

        this.canDoDeadTileAnalysis = true;

        this.isolatedEdgeBruteForce = null;

        this.validWeb = true;
        this.recursions = 0;

        // can't have less than zero mines
        if (minesLeft < 0) {
            this.validWeb = false;
            return;
        }

        // generate a BoxWitness for each witness tile and also create a list of pruned witnesses for the brute force search
        let pruned = 0;
        for (let i = 0; i < allWitnesses.length; i++) {
            const wit = allWitnesses[i];

            const boxWit = new BoxWitness(this.board, wit);

            // can't have too many or too few mines 
            if (boxWit.minesToFind < 0 || boxWit.minesToFind > boxWit.tiles.length) {
                this.validWeb = false;
            }

            // if the witness is a duplicate then don't store it
            let duplicate = false;
            for (let j = 0; j < this.boxWitnesses.length; j++) {

                const w = this.boxWitnesses[j];

                if (w.equivalent(boxWit)) {
                    //if (boardState.getWitnessValue(w) - boardState.countAdjacentConfirmedFlags(w) != boardState.getWitnessValue(wit) - boardState.countAdjacentConfirmedFlags(wit)) {
                    //    boardState.display(w.display() + " and " + wit.display() + " share unrevealed squares but have different mine totals!");
                    //    validWeb = false;
                    //}
                    duplicate = true;
                    break;
                }
            }
            if (!duplicate) {
                this.prunedWitnesses.push(boxWit);
             } else {
                pruned++;
            }
            this.boxWitnesses.push(boxWit);  // all witnesses are needed for the probability engine
        }
        this.writeToConsole("Pruned " + pruned + " witnesses as duplicates");
        this.writeToConsole("There are " + this.boxWitnesses.length + " Box witnesses");

		// allocate each of the witnessed squares to a box
		let uid = 0;
		for (let i=0; i < this.witnessed.length; i++) {
			
			const tile = this.witnessed[i];
			
			let count = 0;
			
			// count how many adjacent witnesses the tile has
			for (let j=0; j < allWitnesses.length; j++) {
				if (tile.isAdjacent(allWitnesses[j])) {
					count++;
				}
			}
			
            // see if the witnessed tile fits any existing boxes
            let found = false;
			for (let j=0; j < this.boxes.length; j++) {
				
				if (this.boxes[j].fits(tile, count)) {
					this.boxes[j].add(tile);
					found = true;
					break;
				}
				
			}
			
			// if not found create a new box and store it
			if (!found) {
                this.boxes.push(new Box(this.boxWitnesses, tile, uid++));
			}

        }

        // calculate the min and max mines for each box 
        for (let i = 0; i < this.boxes.length; i++) {
            const box = this.boxes[i];
            box.calculate(this.minesLeft);
            //console.log("Box " + box.tiles[0].asText() + " has min mines = " + box.minMines + " and max mines = " + box.maxMines);
        }

        // Report how many boxes each witness is adjacent to
        //for (var i = 0; i < this.boxWitnesses.length; i++) {
        //    var boxWit = this.boxWitnesses[i];
        //      console.log("Witness " + boxWit.tile.asText() + " is adjacent to " + boxWit.boxes.length + " boxes and has " + boxWit.minesToFind + " mines to find");
        //}

        Object.seal(this); // prevent new values being created

 	}

    checkForUnavoidableGuess() {

        for (let i = 0; i < this.prunedWitnesses.length; i++) {
            const witness = this.prunedWitnesses[i];

            if (witness.minesToFind == 1 && witness.tiles.length == 2) {

                //console.log("Witness " + witness.tile.asText() + " is a possible unavoidable guess witness");
                let unavoidable = true;
                // if every monitoring tile also monitors all the other tiles then it can't provide any information
                check: for (let j = 0; j < witness.tiles.length; j++) {
                    const tile = witness.tiles[j];

                    // get the witnesses monitoring this tile
                    for (let adjTile of this.board.getAdjacent(tile)) {

                        // ignore tiles which are mines
                        if (adjTile.isSolverFoundBomb()) {
                            continue;
                        }

                        // are we one of the tiles other tiles, if so then no need to check
                        let toCheck = true;
                        for (let otherTile of witness.tiles) {
                            if (otherTile.isEqual(adjTile)) {
                                toCheck = false;
                                break;
                            }
                        }

                        // if we are monitoring and not a mine then see if we are also monitoring all the other mines
                        if (toCheck) {
                            for (let otherTile of witness.tiles) {
                                if (!adjTile.isAdjacent(otherTile)) {

                                    //console.log("Tile " + adjTile.asText() + " is not monitoring all the other witnessed tiles");
                                    unavoidable = false;
                                    break check;
                                }
                            }
                        }
                    }
                }
                if (unavoidable) {
                    this.writeToConsole("Tile " + witness.tile.asText() + " is an unavoidable guess");
                    return witness.tiles[0];
                } 
            }
        }

        return null;
    }


    checkForUnavoidable5050() {

        const links = [];

        for (let i = 0; i < this.prunedWitnesses.length; i++) {
            const witness = this.prunedWitnesses[i];

            if (witness.minesToFind == 1 && witness.tiles.length == 2) {

                // create a new link
                const link = new Link();
                link.tile1 = witness.tiles[0];
                link.tile2 = witness.tiles[1];

                //console.log("Witness " + witness.tile.asText() + " is a possible unavoidable guess witness");
                let unavoidable = true;
                // if every monitoring tile also monitors all the other tiles then it can't provide any information
                for (let j = 0; j < witness.tiles.length; j++) {
                    const tile = witness.tiles[j];

                    // get the witnesses monitoring this tile
                    for (let adjTile of this.board.getAdjacent(tile)) {

                        // ignore tiles which are mines
                        if (adjTile.isSolverFoundBomb()) {
                            continue;
                        }

                        // are we one of the tiles other tiles, if so then no need to check
                        let toCheck = true;
                        for (let otherTile of witness.tiles) {
                            if (otherTile.isEqual(adjTile)) {
                                toCheck = false;
                                break;
                            }
                        }

                        // if we are monitoring and not a mine then see if we are also monitoring all the other mines
                        if (toCheck) {
                            for (let otherTile of witness.tiles) {
                                if (!adjTile.isAdjacent(otherTile)) {

                                    //console.log("Tile " + adjTile.asText() + " is not monitoring all the other witnessed tiles");
                                    link.trouble.push(adjTile);
                                    if (tile.isEqual(link.tile1)) {
                                        link.closed1 = false;
                                    } else {
                                        link.closed2 = false;
                                    }

                                    unavoidable = false;
                                    //break check;
                                }
                            }
                        }
                    }
                }
                if (unavoidable) {
                    this.writeToConsole("Tile " + link.tile1.asText() + " is an unavoidable 50/50 guess");
                    return this.notDead([link.tile1, link.tile2]);
                }

                links.push(link);
            }
        }

        // this is the area the 50/50 spans
        let area5050 = [];

        // try and connect 2 or links together to form an unavoidable 50/50
        for (let link of links) {
            if (!link.processed && (link.closed1 && !link.closed2 || !link.closed1 && link.closed2)) {  // this is the XOR operator, so 1 and only 1 of these is closed 

                let openTile;
                let extensions = 0;
                if (!link.closed1) {
                    openTile = link.tile1;
                } else {
                    openTile = link.tile2;
                }

                area5050 = [link.tile1, link.tile2];

                link.processed = true;

                let noMatch = false;
                while (openTile != null && !noMatch) {

                    noMatch = true;
                    for (let extension of links) {
                        if (!extension.processed) {

                            if (extension.tile1.isEqual(openTile)) {
                                extensions++;
                                extension.processed = true;
                                noMatch = false;

                                // accumulate the trouble tiles as we progress;
                                link.trouble.push(...extension.trouble);
                                area5050.push(extension.tile2);   // tile2 is the new tile

                                if (extension.closed2) {
                                    if (extensions % 2 == 0 && this.noTrouble(link, area5050)) {
                                        this.writeToConsole("Tile " + openTile.asText() + " is an unavoidable guess, with " + extensions + " extensions");
                                        return this.notDead(area5050);
                                    } else {
                                        this.writeToConsole("Tile " + openTile.asText() + " is a closed extension with " + (extensions + 1) + " parts");
                                        openTile = null;
                                    }
                                } else {  // found an open extension, now look for an extension for this
                                    openTile = extension.tile2;
                                }
                                break;
                            }
                            if (extension.tile2.isEqual(openTile)) {
                                extensions++;
                                extension.processed = true;
                                noMatch = false;

                                // accumulate the trouble tiles as we progress;
                                link.trouble.push(...extension.trouble);
                                area5050.push(extension.tile1);   // tile 1 is the new tile

                                if (extension.closed1) {
                                    if (extensions % 2 == 0 && this.noTrouble(link, area5050)) {
                                        this.writeToConsole("Tile " + openTile.asText() + " is an unavoidable guess, with " + extensions + " extensions");
                                        return this.notDead(area5050);
                                    } else {
                                        this.writeToConsole("Tile " + openTile.asText() + " is a closed extension with " + (extensions + 1) + " parts");
                                        openTile = null;
                                    }

                                } else {  // found an open extension, now look for an extension for this
                                    openTile = extension.tile1;
                                }

                                break;
                            }

                        }

                    }

                }

            }
        }

        return null;
    }

    // return a tile which isn't dead
    notDead(area) {

        for (let tile of area) {
            let dead = false;
            for (let deadTile of this.deadTiles) {
                if (deadTile.isEqual(tile)) {
                    dead = true;
                    break;
                }
            }
            if (!dead) {
                return tile;
            }
        }

        // if they are all dead, return the first
        return area[0];
    }

    noTrouble(link, area) {

        // each trouble location must be adjacent to 2 tiles in the extended 50/50
        top: for (let tile of link.trouble) {

            for (let tile5050 of area) {
                if (tile.isEqual(tile5050)) {
                    continue top;    //if a trouble tile is part of the 50/50 it isn't trouble
                }
            }


            let adjCount = 0;
            for (let tile5050 of area) {
                if (tile.isAdjacent(tile5050)) {
                    adjCount++;
                }
            }
            if (adjCount % 2 !=0) {
                this.writeToConsole("Trouble Tile " + tile.asText() + " isn't adjacent to an even number of tiles in the extended candidate 50/50, adjacent " + adjCount + " of " + area.length);
                return false;
            }
        }

        return true;

    }

    // calculate a probability for each un-revealed tile on the board
	process() {

        // if the board isn't valid then solution count is zero
        if (!this.validWeb) {
            this.finalSolutionsCount = BigInt(0);
            this.clearCount = 0;
            return;
        }

        const peStart = Date.now();

        // create an array showing which boxes have been procesed this iteration - none have to start with
        this.mask = Array(this.boxes.length).fill(false);

        // look for places which could be dead
        this.getCandidateDeadLocations();

		// create an initial solution of no mines anywhere 
        this.heldProbs.push(new ProbabilityLine(this.boxes.length, BigInt(1)));
		
		// add an empty probability line to get us started
        this.workingProbs.push(new ProbabilityLine(this.boxes.length, BigInt(1)));
		
        let nextWitness = this.findFirstWitness();

        while (nextWitness != null) {

            //console.log("Probability engine processing witness " + nextWitness.boxWitness.tile.asText());

            // mark the new boxes as processed - which they will be soon
            for (let i = 0; i < nextWitness.newBoxes.length; i++) {
                this.mask[nextWitness.newBoxes[i].uid] = true;
            }

            this.workingProbs = this.mergeProbabilities(nextWitness);

            nextWitness = this.findNextWitness(nextWitness);

        }

        // if we don't have any local clears then do a full probability determination
        if (this.localClears.length == 0) {
            this.calculateBoxProbabilities();
        } else {
            this.bestProbability = 1;
        }

        if (this.fullAnalysis) {
            this.writeToConsole("The probability engine did a full analysis - probability data is available")
        } else {
            this.writeToConsole("The probability engine did a truncated analysis - probability data is not available")
        }

        this.duration = Date.now() - peStart;

		
	}


    // take the next witness details and merge them into the currently held details
    mergeProbabilities(nw) {

        const newProbs = [];

        for (let i = 0; i < this.workingProbs.length; i++) {

            const pl = this.workingProbs[i];

            const missingMines = nw.boxWitness.minesToFind - this.countPlacedMines(pl, nw);

            if (missingMines < 0) {
                //console.log("Missing mines < 0 ==> ignoring line");
                // too many mines placed around this witness previously, so this probability can't be valid
            } else if (missingMines == 0) {
                //console.log("Missing mines = 0 ==> keeping line as is");
                newProbs.push(pl);   // witness already exactly satisfied, so nothing to do
            } else if (nw.newBoxes.length == 0) {
                //console.log("new boxes = 0 ==> ignoring line since nowhere for mines to go");
                // nowhere to put the new mines, so this probability can't be valid
            } else {
                
                const result = this.distributeMissingMines(pl, nw, missingMines, 0);
                newProbs.push(...result);

            }

        }

        // flag the last set of details as processed
        nw.boxWitness.processed = true;

        for (let i = 0; i < nw.newBoxes.length; i++) {
            nw.newBoxes[i].processed = true;
        }

        //if we haven't compressed yet and we are still a small edge then don't compress
        if (newProbs.length < 100 && this.canDoDeadTileAnalysis) {
            return newProbs;
        }

        // about to compress the line
        this.canDoDeadTileAnalysis = false;

        const boundaryBoxes = [];
        for (let i = 0; i < this.boxes.length; i++) {
            const box = this.boxes[i];
            let notProcessed = false;
            let processed = false;
            for (let j = 0; j < box.boxWitnesses.length; j++) {
                if (box.boxWitnesses[j].processed) {
                    processed = true;
                } else {
                    notProcessed = true;
                }
                if (processed && notProcessed) {
                    //boardState.display("partially processed box " + box.getUID());
                    boundaryBoxes.push(box);
                    break;
                }
            }
        }
        //boardState.display("Boxes partially processed " + boundaryBoxes.size());

        const sorter = new MergeSorter(boundaryBoxes);

        const crunched = this.crunchByMineCount(newProbs, sorter);

        //if (newProbs.length == 0) {
        //     console.log("Returning no lines from merge probability !!");
        //}

         return crunched;

    }

    // counts the number of mines already placed
    countPlacedMines(pl, nw) {

        let result = 0;

        for (let i = 0; i < nw.oldBoxes.length; i++) {

            const b = nw.oldBoxes[i];

            result = result + pl.allocatedMines[b.uid];
        }

        return result;
    }

    // this is used to recursively place the missing Mines into the available boxes for the probability line
    distributeMissingMines(pl, nw,  missingMines, index) {

        //console.log("Distributing " + missingMines + " missing mines to box " + nw.newBoxes[index].uid);

        this.recursions++;
        if (this.recursions % 1000 == 0) {
            console.log("Probability Engine recursision = " + this.recursions);
        }

        const result = [];

        // if there is only one box left to put the missing mines we have reach the end of this branch of recursion
        if (nw.newBoxes.length - index == 1) {
            // if there are too many for this box then the probability can't be valid
            if (nw.newBoxes[index].maxMines < missingMines) {
                //console.log("Abandon (1)");
                return result;
            }
            // if there are too few for this box then the probability can't be valid
            if (nw.newBoxes[index].minMines > missingMines) {
                //console.log("Abandon (2)");
                return result;
            }
            // if there are too many for this game then the probability can't be valid
            if (pl.mineCount + missingMines > this.maxTotalMines) {
                //console.log("Abandon (3)");
                return result;
            }

            // otherwise place the mines in the probability line
            //pl.mineBoxCount[nw.newBoxes[index].uid] = BigInt(missingMines);
            //pl.mineCount = pl.mineCount + missingMines;
            result.push(this.extendProbabilityLine(pl, nw.newBoxes[index], missingMines));
            //console.log("Distribute missing mines line after " + pl.mineBoxCount);
            return result;
        }


        // this is the recursion
        const maxToPlace = Math.min(nw.newBoxes[index].maxMines, missingMines);

        for (let i = nw.newBoxes[index].minMines; i <= maxToPlace; i++) {
            const npl = this.extendProbabilityLine(pl, nw.newBoxes[index], i);

            const r1 = this.distributeMissingMines(npl, nw, missingMines - i, index + 1);
            result.push(...r1);
        }

        return result;

    }

    // create a new probability line by taking the old and adding the mines to the new Box
    extendProbabilityLine(pl, newBox, mines) {

        //console.log("Extended probability line: Adding " + mines + " mines to box " + newBox.uid);
        //console.log("Extended probability line before" + pl.mineBoxCount);

        // there are less ways to place the mines if we know one of the tiles doesn't contain a mine
        const modifiedTilesCount = newBox.tiles.length - newBox.emptyTiles;

        const combination = SolutionCounter.SMALL_COMBINATIONS[modifiedTilesCount][mines];
        //const combination = ProbabilityEngine.SMALL_COMBINATIONS[newBox.tiles.length][mines];
        const bigCom = BigInt(combination);

        const newSolutionCount = pl.solutionCount * bigCom;

        const result = new ProbabilityLine(this.boxes.length, newSolutionCount);

        result.mineCount = pl.mineCount + mines;
 
        // copy the probability array

        if (combination != 1) {
            for (let i = 0; i < pl.mineBoxCount.length; i++) {
                result.mineBoxCount[i] = pl.mineBoxCount[i] * bigCom;
            }
        } else {
            result.mineBoxCount = pl.mineBoxCount.slice();
        }

        result.mineBoxCount[newBox.uid] = BigInt(mines) * result.solutionCount;

        result.allocatedMines = pl.allocatedMines.slice();
        result.allocatedMines[newBox.uid] = mines;

        //console.log("Extended probability line after " + result.mineBoxCount);

        return result;
    }


    // this combines newly generated probabilities with ones we have already stored from other independent sets of witnesses
    storeProbabilities() {

        //console.log("At store probabilities");

        const result = [];

        //this.checkCandidateDeadLocations();

        if (this.workingProbs.length == 0) {
            //this.writeToConsole("working probabilites list is empty!!", true);
            this.heldProbs = [];
        	return;
        } 

        // crunch the new ones down to one line per mine count
        //var crunched = this.crunchByMineCount(this.workingProbs);

        const crunched = this.workingProbs;

        if (crunched.length == 1) {
            this.checkEdgeIsIsolated();
        }

        //solver.display("New data has " + crunched.size() + " entries");

        for (let i = 0; i < crunched.length; i++) {

            pl = crunched[i];

            for (let j = 0; j < this.heldProbs.length; j++) {

                const epl = this.heldProbs[j];

                const npl = new ProbabilityLine(this.boxes.length);

                npl.mineCount = pl.mineCount + epl.mineCount;

                if (npl.mineCount <= this.maxTotalMines) {

                    npl.solutionCount = pl.solutionCount * epl.solutionCount;

                    for (let k = 0; k < npl.mineBoxCount.length; k++) {

                        const w1 = pl.mineBoxCount[k] * epl.solutionCount;
                        const w2 = epl.mineBoxCount[k] * pl.solutionCount;
                        npl.mineBoxCount[k] = w1 + w2;

                    }
                    result.push(npl);

                }
            }
        }

        // sort into mine order 
        result.sort(function (a, b) { return a.mineCount - b.mineCount });

        this.heldProbs = [];

        // if result is empty this is an impossible position
        if (result.length == 0) {
            return;
        }

        // and combine them into a single probability line for each mine count
        let mc = result[0].mineCount;
        let npl = new ProbabilityLine(this.boxes.length);
        npl.mineCount = mc;

        for (let i = 0; i < result.length; i++) {

            var pl = result[i];

            if (pl.mineCount != mc) {
                this.heldProbs.push(npl);
                mc = pl.mineCount;
                npl = new ProbabilityLine(this.boxes.length);
                npl.mineCount = mc;
            }
            npl.solutionCount = npl.solutionCount + pl.solutionCount;

            for (let j = 0; j < pl.mineBoxCount.length; j++) {
                npl.mineBoxCount[j] = npl.mineBoxCount[j] + pl.mineBoxCount[j];
            }
        }

        this.heldProbs.push(npl);

    }

    crunchByMineCount(target, sorter) {

        if (target.length == 0) {
            return target;
         }

        // sort the solutions by number of mines
        target.sort(function (a, b) { return sorter.compare(a,b) });

        const result = [];

        let current = null;

        for (let i = 0; i < target.length; i++) {

            const pl = target[i];

            if (current == null) {
                current = target[i];
            } else if (sorter.compare(current, pl) != 0) {
                result.push(current);
                current = pl;
            } else {
                this.mergeLineProbabilities(current, pl);
            }

        }

        //if (npl.mineCount >= minTotalMines) {
        result.push(current);
        //}	

        this.writeToConsole(target.length + " Probability Lines compressed to " + result.length); 

        return result;

    }

    // calculate how many ways this solution can be generated and roll them into one
    mergeLineProbabilities(npl, pl) {

        /*
        var solutions = BigInt(1);
        for (var i = 0; i < pl.mineBoxCount.length; i++) {
            solutions = solutions * BigInt(this.SMALL_COMBINATIONS[this.boxes[i].tiles.length][pl.mineBoxCount[i]]);
        }

        npl.solutionCount = npl.solutionCount + solutions;
        */

        npl.solutionCount = npl.solutionCount + pl.solutionCount;

        for (let i = 0; i < pl.mineBoxCount.length; i++) {
            if (this.mask[i]) {  // if this box has been involved in this solution - if we don't do this the hash gets corrupted by boxes = 0 mines because they weren't part of this edge
                npl.mineBoxCount[i] = npl.mineBoxCount[i] + pl.mineBoxCount[i];
            }

        }

    }

    // return any witness which hasn't been processed
    findFirstWitness() {

        for (let i = 0; i < this.boxWitnesses.length; i++) {
            const boxWit = this.boxWitnesses[i];
            if (!boxWit.processed) {
                return new NextWitness(boxWit);
            }
        }

        return null;
    }

    // look for the next witness to process
    findNextWitness(prevWitness) {

        let bestTodo = 99999;
        let bestWitness = null;

        // and find a witness which is on the boundary of what has already been processed
        for (let i = 0; i < this.boxes.length; i++) {
            const b = this.boxes[i];
            if (b.processed) {
                for (let j = 0; j < b.boxWitnesses.length; j++) {
                    const w = b.boxWitnesses[j];
                    if (!w.processed) {
                        let todo = 0;
                        for (let k = 0; k < w.boxes.length; k++) {
                            const b1 = w.boxes[k];

                            if (!b1.processed) {
                                todo++;
                            }
                        }
                        if (todo == 0) {    // prioritise the witnesses which have the least boxes left to process
                            return new NextWitness(w);
                        } else if (todo < bestTodo) {
                            bestTodo = todo;
                            bestWitness = w;
                        }
                    }
                }
            }
        }

        if (bestWitness != null) {
            return new NextWitness(bestWitness);
        } else {
            this.writeToConsole("Ending independent edge");
        }

        // if we are down here then there is no witness which is on the boundary, so we have processed a complete set of independent witnesses 

        // if playing for efficiency check all edges, slower but we get better information
        if (this.playStyle != PLAY_STYLE_EFFICIENCY && this.playStyle != PLAY_STYLE_NOFLAGS_EFFICIENCY && !this.options.fullProbability) {

            // look to see if this sub-section of the edge has any certain clears
            for (let i = 0; i < this.mask.length; i++) {
                if (this.mask[i]) {

                    let isClear = true;
                    for (let j = 0; j < this.workingProbs.length; j++) {
                        const wp = this.workingProbs[j];
                        if (wp.mineBoxCount[i] != 0) {
                            isClear = false;
                            break;
                        }
                    }
                    if (isClear) {
                        // if the box is locally clear then store the tiles in it
                        for (let j = 0; j < this.boxes[i].tiles.length; j++) {

                            const tile = this.boxes[i].tiles[j];

                            this.writeToConsole(tile.asText() + " has been determined to be locally clear");
                            this.localClears.push(tile);
                        }
                    }

                    let isFlag = true;
                    for (let j = 0; j < this.workingProbs.length; j++) {
                        const wp = this.workingProbs[j];
                        if (wp.mineBoxCount[i] != wp.solutionCount * BigInt(this.boxes[i].tiles.length)) {
                            isFlag = false;
                            break;
                        }
                    }
                    if (isFlag) {
                        // if the box contains all mines then store the tiles in it
                        for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                            const tile = this.boxes[i].tiles[j];
                            this.writeToConsole(tile.asText() + " has been determined to be locally a mine");
                            this.minesFound.push(tile);
                        }
                    }
                }
            }

            // if we have found some local clears then stop and use these
            if (this.localClears.length > 0) {
                return null;
            }

        }
 

        //independentGroups++;

        this.checkCandidateDeadLocations(this.canDoDeadTileAnalysis);

        // if we haven't compressed yet then do it now
        if (this.canDoDeadTileAnalysis) {
            const sorter = new MergeSorter();
            this.workingProbs = this.crunchByMineCount(this.workingProbs, sorter);
        } else {
            this.canDoDeadTileAnalysis = true;
        }

        // since we have calculated all the mines in an independent set of witnesses we can crunch them down and store them for later

        // get an unprocessed witness
        const nw = this.findFirstWitness();
        if (nw != null) {
            this.writeToConsole("Starting a new independent edge");
        }

        // Store the probabilities for later consolidation
        this.storeProbabilities();

        // reset the working array so we can start building up one for the new set of witnesses
        this.workingProbs = [new ProbabilityLine(this.boxes.length, BigInt(1))];
 
        // reset the mask indicating that no boxes have been processed 
        this.mask.fill(false);
 

        // return the next witness to process
        return nw;

    }


    // check the candidate dead locations with the information we have - remove those that aren't dead
    checkCandidateDeadLocations(checkPossible) {

        let completeScan;
        if (this.TilesOffEdge == 0) {
            completeScan = true;   // this indicates that every box has been considered in one sweep (only 1 independent edge)
            for (let i = 0; i < this.mask.length; i++) {
                if (!this.mask[i]) {
                    completeScan = false;
                    break;
                }
            }
            if (completeScan) {
                this.writeToConsole("This is a complete scan");
            } else {
                this.writeToConsole("This is not a complete scan");
            }
        } else {
            completeScan = false;
            this.writeToConsole("This is not a complete scan because there are squares off the edge");
        }


        for (let i = 0; i < this.deadCandidates.length; i++) {

            const dc = this.deadCandidates[i];

            if (dc.isAlive) {  // if this location isn't dead then no need to check any more
                continue;
            }

            // only do the check if all the boxes have been analysed in this probability iteration
            let boxesInScope = 0;
            for (let j = 0; j < dc.goodBoxes.length; j++) {
                const b = dc.goodBoxes[j];
                if (this.mask[b.uid]) {
                    boxesInScope++;
                }
            }
            for (let j = 0; j < dc.badBoxes.length; j++) {
                const b = dc.badBoxes[j];
                if (this.mask[b.uid]) {
                    boxesInScope++;
                }
            }
            if (boxesInScope == 0) {
                continue;
            } else if (boxesInScope != dc.goodBoxes.length + dc.badBoxes.length) {
                this.writeToConsole("Location " + dc.candidate.asText() + " has some boxes in scope and some out of scope so assumed alive");
                dc.isAlive = true;
                continue;
            }

            //if we can't do the check because the edge has been compressed mid process then assume alive
            if (!checkPossible) {
                this.writeToConsole("Location " + dc.candidate.asText() + " was on compressed edge so assumed alive");
                dc.isAlive = true;
                continue;
            }

            let okay = true;
            let mineCount = 0;
            line: for (let j = 0; j < this.workingProbs.length; j++) {

                const pl = this.workingProbs[j];

                if (completeScan && pl.mineCount != this.minesLeft) {
                    continue line;
                }

                // ignore probability lines where the candidate is a mine
                if (pl.allocatedMines[dc.myBox.uid] == dc.myBox.tiles.length) {
                    mineCount++;
                    continue line;
                }

                // all the bad boxes must be zero
                for (let k = 0; k < dc.badBoxes.length; k++) {

                    const b = dc.badBoxes[k];

                    let neededMines;
                    if (b.uid == dc.myBox.uid) {
                        neededMines = BigInt(b.tiles.length - 1) * pl.solutionCount;
                    } else {
                        neededMines = BigInt(b.tiles.length) * pl.solutionCount;
                    }

                    // a bad box must have either no mines or all mines
                    if (pl.mineBoxCount[b.uid] != 0 && pl.mineBoxCount[b.uid] != neededMines) {
                        this.writeToConsole("Location " + dc.candidate.asText() + " is not dead because a bad box has neither zero or all mines: " + pl.mineBoxCount[b.uid] + "/" + neededMines);
                        okay = false;
                        break line;
                    }
                }

                let tally = 0;
                // the number of mines in the good boxes must always be the same
                for (let k = 0; k < dc.goodBoxes.length; k++) {
                    const b = dc.goodBoxes[k];
                    tally = tally + pl.allocatedMines[b.uid];
                }
                //boardState.display("Location " + dc.candidate.display() + " has mine tally " + tally);
                if (dc.firstCheck) {
                    dc.total = tally;
                    dc.firstCheck = false;
                } else {
                    if (dc.total != tally) {
                        this.writeToConsole("Location " + dc.candidate.asText() + " is not dead because the sum of mines in good boxes is not constant. Was "
                            + dc.total + " now " + tally + ". Mines in probability line " + pl.mineCount);
                        okay = false;
                        break;
                    }
                }
            }

            // if a check failed or every this tile is a mine for every solution then it is alive
            if (!okay || mineCount == this.workingProbs.length) {
                dc.isAlive = true;
            }

        }

    }


    // find a list of locations which could be dead
    getCandidateDeadLocations() {

        // for each square on the edge
        for (let i = 0; i < this.witnessed.length; i++) {

            const tile = this.witnessed[i];

            const adjBoxes = this.getAdjacentBoxes(tile);

            if (adjBoxes == null) {  // this happens when the square isn't fully surrounded by boxes
                continue;
            }

            const dc = new DeadCandidate();
            dc.candidate = tile;
            dc.myBox = this.getBox(tile);

            for (let j = 0; j < adjBoxes.length; j++) {

                const box = adjBoxes[j];

                let good = true;
                for (let k = 0; k < box.tiles.length; k++) {

                    const square = box.tiles[k];

                    if (!square.isAdjacent(tile) && !(square.index == tile.index)) {
                        good = false;
                        break;
                    }
                }
                if (good) {
                    dc.goodBoxes.push(box);
                } else {
                    dc.badBoxes.push(box);
                }

            }

            if (dc.goodBoxes.length == 0 && dc.badBoxes.length == 0) {
                this.writeToConsole(dc.candidate.asText() + " is lonely since it has no open tiles around it");
                this.lonelyTiles.push(dc);
            } else {
                this.deadCandidates.push(dc);
            }
            

        }

        for (let i = 0; i < this.deadCandidates.length; i++) {
            const dc = this.deadCandidates[i];
            this.writeToConsole(dc.candidate.asText() + " is candidate dead with " + dc.goodBoxes.length + " good boxes and " + dc.badBoxes.length + " bad boxes");
        }

    }

    // get the box containing this tile
    getBox(tile) {

        for (let i = 0; i < this.boxes.length; i++) {
            if (this.boxes[i].contains(tile)) {
                return this.boxes[i];
            }
        }

        //this.writeToConsole("ERROR - tile " + tile.asText() + " doesn't belong to a box");

        return null;
    }

    // return all the boxes adjacent to this tile
    getAdjacentBoxes(loc) {

        const result = [];

        const adjLocs = this.board.getAdjacent(loc);

         // get each adjacent location
        for (let i = 0; i < adjLocs.length; i++) {

            let adjLoc = adjLocs[i];

            // we only want adjacent tile which are un-revealed
            if (!adjLoc.isCovered() || adjLoc.isSolverFoundBomb()) {
                continue;
            }

            // find the box it is in
            let boxFound = false;
            for (let j = 0; j < this.boxes.length; j++) {

                const box = this.boxes[j];

                if (box.contains(adjLoc)) {
                    boxFound = true;
                    // is the box already included?
                    let found = false;
                    for (let k = 0; k < result.length; k++) {

                        if (box.uid == result[k].uid) {
                            found = true;
                            break;
                        }
                    }
                    // if not add it
                    if (!found) {
                        result.push(box);
                        //sizeOfBoxes = box.getSquares().size();
                    }
                }
            }

            // if a box can't be found for the adjacent square then the location can't be dead
            if (!boxFound) {
                return null;
            }

        }

        return result;

    }

    // an edge is isolated if every tile on it is completely surrounded by boxes also on the same edge
    checkEdgeIsIsolated() {

        const edgeTiles = new Set();
        const edgeWitnesses = new Set();

        let everything = true;

        // load each tile on this edge into a set
        for (let i = 0; i < this.mask.length; i++) {
            if (this.mask[i]) {
                //edgeTiles.add(...this.boxes[i].tiles);
                for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                    edgeTiles.add(this.boxes[i].tiles[j]);
                }

                for (let j = 0; j < this.boxes[i].boxWitnesses.length; j++) {
                    edgeWitnesses.add(this.boxes[i].boxWitnesses[j].tile);
                }
 
            } else {
                everything = false;
            }
        }

        //var text = "";
        //for (var i = 0; i < edgeTiles.size; i++) {
        //    text = text + edgeTiles[i].asText() + " ";
        //}
        //console.log(text);

        // if this edge is everything then it isn't an isolated edge
        //if (everything) {
        //    this.writeToConsole("Not isolated because the edge is everything");
        //    return false;
        //}

        if (this.isolatedEdgeBruteForce != null && edgeTiles.size >= this.isolatedEdgeBruteForce.tiles.length) {
            this.writeToConsole("Already found an isolated edge of smaller size");
        }

        // check whether every tile adjacent to the tiles on the edge is itself on the edge
        for (let i = 0; i < this.mask.length; i++) {
            if (this.mask[i]) {
                for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                    const tile = this.boxes[i].tiles[j];
                    const adjTiles = this.board.getAdjacent(tile);
                    for (let k = 0; k < adjTiles.length; k++) {
                        const adjTile = adjTiles[k];
                        if (adjTile.isCovered() && !adjTile.isSolverFoundBomb() && !edgeTiles.has(adjTile)) {
                            this.writeToConsole("Not isolated because a tile's adjacent tiles isn't on the edge: " + tile.asText() + " ==> " + adjTile.asText());
                            return false;
                        }
                    }
                }
            }
        }

        this.writeToConsole("*** Isolated Edge found ***");

        const tiles = [...edgeTiles];
        const witnesses = [...edgeWitnesses];
        const mines = this.workingProbs[0].mineCount;
        // build a web of the isolated edge and use it to build a brute force
        const isolatedEdge = new ProbabilityEngine(this.board, witnesses, tiles, tiles.length, mines, this.options);
        isolatedEdge.generateIndependentWitnesses();
        const iterator = new WitnessWebIterator(isolatedEdge, tiles, -1);

        const bruteForce = new Cruncher(this.board, iterator);
 
        this.isolatedEdgeBruteForce = bruteForce;

        return true;
    }

    // determine a set of independent witnesses which can be used to brute force the solution space more efficiently then a basic 'pick r from n' 
    generateIndependentWitnesses() {

        this.remainingSquares = this.witnessed.length;

        // find a set of witnesses which don't share any squares (there can be many of these, but we just want one to use with the brute force iterator)
        for (let i = 0; i < this.prunedWitnesses.length; i++) {

            const w = this.prunedWitnesses[i];

            //console.log("Checking witness " + w.tile.asText() + " for independence");

            let okay = true;
            for (let j = 0; j < this.independentWitnesses.length; j++) {

                const iw = this.independentWitnesses[j];

                if (w.overlap(iw)) {
                    okay = false;
                    break;
                }
            }

            // split the witnesses into dependent ones and independent ones 
            if (okay) {
                this.remainingSquares = this.remainingSquares - w.tiles.length;
                this.independentIterations = this.independentIterations * this.BINOMIAL.combination(w.minesToFind, w.tiles.length);
                this.independentMines = this.independentMines + w.minesToFind;
                this.independentWitnesses.push(w);  
            } else {
                this.dependentWitnesses.push(w);
            }
        }

        this.writeToConsole("Calculated " + this.independentWitnesses.length + " independent witnesses");

    }

    divideBigInt(numerator, denominator, dp) {

        const work = numerator * power10n[dp] / denominator;
    
        const result = Number(work) / power10[dp];
    
        return result;
    }

    // here we expand the localised solution to one across the whole board and
    // sum them together to create a definitive probability for each box
    calculateBoxProbabilities() {

        const tally = [];
        for (let i = 0; i < this.boxes.length; i++) {
            tally[i] = BigInt(0);
        }

        // total game tally
        let totalTally = BigInt(0);

        // outside a box tally
        let outsideTally = BigInt(0);

        //console.log("There are " + this.heldProbs.length + " different mine counts on the edge");

        // calculate how many mines 
        for (let i = 0; i < this.heldProbs.length; i++) {

            const pl = this.heldProbs[i];

            //console.log("Mine count is " + pl.mineCount + " with solution count " + pl.solutionCount + " mineBoxCount = " + pl.mineBoxCount);

            if (pl.mineCount >= this.minTotalMines) {    // if the mine count for this solution is less than the minimum it can't be valid
 
                const mult = this.BINOMIAL.combination(this.minesLeft - pl.mineCount, this.TilesOffEdge);  //# of ways the rest of the board can be formed
                const newSolutions = mult * pl.solutionCount;

                this.writeToConsole(newSolutions + " solutions with " + pl.mineCount + " mines on Perimeter");

                outsideTally = outsideTally + mult * BigInt(this.minesLeft - pl.mineCount) * (pl.solutionCount);

                // this is all the possible ways the mines can be placed across the whole game
                totalTally = totalTally + newSolutions;

                for (let j = 0; j < tally.length; j++) {
                    //console.log("mineBoxCount " + j + " is " + pl.mineBoxCount[j]);
                    tally[j] = tally[j] + (mult * pl.mineBoxCount[j]) / BigInt(this.boxes[j].tiles.length);
                }
            }

        }

        this.minesFound = [];  // forget any mines we found on edges as we went along, we'll find them again here
        // for each box calculate a probability
        for (let i = 0; i < this.boxes.length; i++) {

            if (totalTally != 0) {
                if (tally[i] == totalTally) {  // a mine
                    //console.log("Box " + i + " contains mines");
                    this.boxProb[i] = 0;

                } else if (tally[i] == 0) {  // safe
                    this.boxProb[i] = 1;
                    this.emptyBoxes.push(this.boxes[i]);

                } else {  // neither mine nor safe
                    this.boxProb[i] = 1 - this.divideBigInt(tally[i], totalTally, 6);
                }

                this.boxes[i].mineTally = tally[i]; 
            } else {
                this.boxProb[i] = 0;
                this.boxes[i].mineTally = 0; 

            }

            //console.log("Box " + i + " has probabality " + this.boxProb[i]);

            // for each tile in the box allocate a probability to it
            for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                if (this.boxProb[i] == 0) {
                    this.minesFound.push(this.boxes[i].tiles[j]);
                }
            }

        }

        // see if the lonely tiles are dead
        for (let i = 0; i < this.lonelyTiles.length; i++) {
            const dc = this.lonelyTiles[i];
            //if (this.boxProb[dc.myBox.uid] != 0 && this.boxProb[dc.myBox.uid] != 1) {   // a lonely tile is dead if not a definite mine or safe
            if (this.boxProb[dc.myBox.uid] != 0) {
                this.writeToConsole("PE found Lonely tile " + dc.candidate.asText() + " is dead with value +" + dc.total);
                this.deadTiles.push(dc.candidate);
            }
        }

        // add the dead locations we found
        for (let i = 0; i < this.deadCandidates.length; i++) {
            const dc = this.deadCandidates[i];
            //if (!dc.isAlive && this.boxProb[dc.myBox.uid] != 0 && this.boxProb[dc.myBox.uid] != 1) {   // if it is dead and not a definite mine or safe
            if (!dc.isAlive && this.boxProb[dc.myBox.uid] != 0) {
                this.writeToConsole("PE found " + dc.candidate.asText() + " to be dead with value +" + dc.total);
                this.deadTiles.push(dc.candidate);
            }
        }

        // avoid divide by zero
        if (this.TilesOffEdge != 0 && totalTally != BigInt(0)) {
            this.offEdgeProbability = 1 - this.divideBigInt(outsideTally, totalTally * BigInt(this.TilesOffEdge), 6);
            this.offEdgeMineTally = outsideTally / BigInt(this.TilesOffEdge);
        } else {
            this.offEdgeProbability = 0;
            this.offEdgeMineTally = 0;
        }

        this.finalSolutionsCount = totalTally;


        // count how many clears we have
        this.localClears = [];
        if (totalTally > 0) {
            for (let i = 0; i < this.boxes.length; i++) {
                if (tally[i] == 0) {
                    this.clearCount = this.clearCount + this.boxes[i].tiles.length;
                    this.localClears.push(...this.boxes[i].tiles);
                }
            }
        }

        // see if we can find a guess which is better than outside the boxes
        let hwm = 0;

        this.bestLivingProbability = this.offEdgeProbability;  // seee if we can do better than the off edge probability

        for (let i = 0; i < this.boxes.length; i++) {

            const b = this.boxes[i];
            let boxLiving = false;

            // a box is dead if all its tiles are dead
            if (this.deadTiles.length > 0) {
                for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                    const tile = this.boxes[i].tiles[j];

                    let tileLiving = true;
                    for (let k = 0; k < this.deadTiles.length; k++) {
                        if (this.deadTiles[k].isEqual(tile)) {
                            tileLiving = false;
                            break;
                        }
                    }
                    if (tileLiving) {
                        boxLiving = true;
                        break;
                    }
                }
            } else {  // if there are no dead tiles then there is nothing to check
                boxLiving = true;
            }


            var prob = this.boxProb[b.uid];
            if (boxLiving || prob == 1) {   // if living or 100% safe then consider this probability
                if (hwm < prob) {
                     hwm = prob;
                }
                if (boxLiving && prob > this.bestLivingProbability) {
                    this.bestLivingProbability = prob;
                }

            }
        }

        this.bestOnEdgeProbability = hwm;

        this.bestProbability = Math.max(this.bestOnEdgeProbability, this.offEdgeProbability);            ;

        this.writeToConsole("Safe tiles " + this.localClears.length + ", Mines found " + this.minesFound.length);
        this.writeToConsole("Off edge probability is " + this.offEdgeProbability);
        this.writeToConsole("Best on edge probability is " + this.bestOnEdgeProbability);
        this.writeToConsole("Best probability is " + this.bestProbability);
        this.writeToConsole("Game has  " + this.finalSolutionsCount + " candidate solutions" );

        this.fullAnalysis = true;
 
    }

    getBestCandidates(freshhold) {

        var best = [];

        //solver.display("Squares left " + this.squaresLeft + " squares analysed " + web.getSquares().size());

        // if the outside probability is the best then return an empty list
        let test;
        if (this.bestProbability == 1) {  // if we have a probability of one then don't allow lesser probs to get a look in
            test = this.bestProbability;
        } else {
            test = this.bestProbability * freshhold;
        }

        this.writeToConsole("Best probability is " + this.bestProbability + " freshhold is " + test);

        for (let i = 0; i < this.boxProb.length; i++) {
            if (this.boxProb[i] >= test) {
                for (let j = 0; j < this.boxes[i].tiles.length; j++) {
                    const squ = this.boxes[i].tiles[j];

                    //  exclude dead tiles 
                    let dead = false;
                    for (let k = 0; k < this.deadTiles.length; k++) {
                        if (this.deadTiles[k].isEqual(squ)) {
                            dead = true;
                            break;
                        }
                    }
                    if (!dead || this.boxProb[i] == 1) {   // if not dead or 100% safe then use the tile
                        best.push(new Action(squ.x, squ.y, this.boxProb[i], ACTION_CLEAR));
                    } else {
                        this.writeToConsole("Tile " + squ.asText() + " is ignored because it is dead");
                    }
 
                }
            }
        }

        // sort in to best order
        best.sort(function (a, b) { return b.prob - a.prob });

        return best;

    }

    // returns an array of 'Tile' which are dead
    getDeadTiles() {

         return this.deadTiles;
    }

    isDead(tile) {

        for (let k = 0; k < this.deadTiles.length; k++) {
            if (this.deadTiles[k].isEqual(tile)) {
                return true;
            }
        }

        return false;
    }

    getProbability(l) {

        for (const b of this.boxes) {
            if (b.contains(l)) {
                return this.boxProb[b.uid];
            }
        }

        return this.offEdgeProbability;
    }

    getFiftyPercenters() {

        const picks = [];

        for (let i = 0; i < this.boxProb.length; i++) {
            if (this.boxProb[i] == 0.5) {
                picks.push(...this.boxes[i].tiles);
            }
        }

        return picks;

    }


    // forces a box to contain a tile which isn't a mine.  If the location isn't in a box false is returned.
     setMustBeEmpty(tile) {

        const box = this.getBox(tile);

        if (box == null) {
            this.validWeb = false;
            return false;
        } else {
            box.incrementEmptyTiles();
        }

        return true;

    }
 
    writeToConsole(text, always) {

        if (always == null) {
            always = false;
        }

        if (this.verbose || always) {
            console.log(text);
        }

    }

}

// solver entry point
async function solver(board, options) {

    // when initialising create some entry points to functions needed from outside
    if (board == null) {
        console.log("Solver Initialisation request received");
        solver.countSolutions = countSolutions;
        return;
    }

    if (options.verbose == null) {
        options.verbose = true;
        writeToConsole("WARN: Verbose parameter not received by the solver, setting verbose = true");
    }

    if (options.playStyle == null) {
        writeToConsole("WARN: playstyle parameter not received by the solver, setting play style to flagging");
        options.playStyle = PLAY_STYLE_FLAGS;
    }

    // this is used to disable all the advanced stuff like BFDA and tie-break
    if (options.advancedGuessing == null) {
        options.advancedGuessing = true;
    }

    // this is used to force a probability engine search
    if (options.fullProbability == null) {
        options.fullProbability = false;
    }

    // a bit of a bodge this variable is used as a global
    let fillerTiles = [];   // this is used by the no-guess board generator 

    let noMoves = 0;
    let cleanActions = [];  // these are the actions to take
    const otherActions = [];    // this is other Actions of interest

    // allow the solver to bring back no moves 5 times. No moves is possible when playing no-flags 
    while (noMoves < 5 && cleanActions.length == 0) {
        noMoves++;
        const actions = await doSolve(board, options);  // look for solutions
        console.log(`actions: ${JSON.stringify(actions.map((action) => action.asText()))}`);

        if (options.playStyle == PLAY_STYLE_EFFICIENCY || options.playStyle == PLAY_STYLE_NOFLAGS_EFFICIENCY) {
            cleanActions = actions;

            // find all the other actions which could be played
            top: for (let tile of board.tiles) {
                if (!tile.isCovered()) {
                    continue;
                }

                // ignore actions which are the primary actions
                for (let action of actions) {
                    if (tile.x == action.x && tile.y == action.y) {
                        //console.log(tile.asText() + " is a primary action");
                        continue top;
                    }
                }
                //console.log(tile.asText() + " mine=" + tile.isSolverFoundBomb() + ", flagged=" + tile.isFlagged() + ", probability=" + tile.probability);
                if (tile.isSolverFoundBomb() && !tile.isFlagged()) {
                    otherActions.push(new Action(tile.getX(), tile.getY(), 0, ACTION_FLAG));
                } else if (tile.probability == 1) {
                    otherActions.push(new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR));
                }
            }

        } else {
            for (let i = 0; i < actions.length; i++) {

                const action = actions[i];

                if (action.action == ACTION_FLAG) {   // if a request to flag
 
                    const tile = board.getTileXY(action.x, action.y);
                    if (!tile.isFlagged()) {   // only accept the flag action if the tile isn't already flagged
                        if (options.playStyle == PLAY_STYLE_FLAGS) {  // if we are flagging
                            cleanActions.push(action);
                        } else {
                            otherActions.push(action);
                        }
                    }
                } else {
                    cleanActions.push(action);
                }
            }
        }
    }

    const reply = {};
    reply.actions = cleanActions;
    reply.fillers = fillerTiles;
    reply.other = otherActions;

    return reply;

    // **** functions below here ****

    // this finds the best moves 
    async function doSolve(board, options) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];
        const unflaggedMines = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        let deadTiles = [];  // used to hold the tiles which have been determined to be dead by either the probability engine or deep analysis

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        console.log("The solver is thinking...");

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            tile.clearHint();  // clear any previous hints

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                tile.setProbability(0);
                if (!tile.isFlagged()) {
                    unflaggedMines.push(tile);
                }
                continue;  // if the tile is a mine then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            if (needsWork) {  // the witness still has some unrevealed adjacent tiles
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        board.setHighDensity(squaresLeft, minesLeft);

        writeToConsole("tiles left = " + squaresLeft);
        writeToConsole("mines left = " + minesLeft);
        writeToConsole("Witnesses  = " + witnesses.length);
        writeToConsole("Witnessed  = " + witnessed.length);

        let result = [];

        // if we are in flagged mode then flag any mines currently unflagged
        if (options.playStyle != PLAY_STYLE_EFFICIENCY && options.playStyle != PLAY_STYLE_NOFLAGS_EFFICIENCY) {
            for (let tile of unflaggedMines) {
                result.push(new Action(tile.getX(), tile.getY(), 0, ACTION_FLAG));
            }
        }

        // if there are no mines left to find the everything else is to be cleared
        if (minesLeft == 0) {
            for (let i = 0; i < allCoveredTiles.length; i++) {
                const tile = allCoveredTiles[i];
                result.push(new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR))
            }
            console.log("No mines left to find all remaining tiles are safe");
            return new EfficiencyHelper(board, witnesses, witnessed, result, options.playStyle, null).process();
        }

        const oldMineCount = result.length;

        // add any trivial moves we've found
        if (options.fullProbability || options.playStyle == PLAY_STYLE_EFFICIENCY || options.playStyle == PLAY_STYLE_NOFLAGS_EFFICIENCY) {
            console.log("Skipping trivial analysis since Probability Engine analysis is required")
        } else {
            result.push(...trivial_actions(board, witnesses));
        }
 
        if (result.length > oldMineCount) {
            console.log("The solver found " + result.length + " trivial safe moves");
            return result;
            /*
            if (options.playStyle != PLAY_STYLE_FLAGS) {
                var mineFound = false;
                var noFlagResult = [];
                for (var i = 0; i < result.length; i++) {

                    var action = result[i];

                    if (action.prob == 0) {   // zero safe probability == mine
                        mineFound = true;
                    } else {   // otherwise we're trying to clear
                        noFlagResult.push(action);
                    }
                }
                if (options.playStyle == PLAY_STYLE_NOFLAGS) {  // flag free but not efficiency, send the clears
                    return noFlagResult;
                } else if (mineFound) { // if we are playing for efficiency and a mine was found then we can't continue. send nothing and try again
                    return [];
                }
                // if we are playing for efficiency and a mine wasn't found then go on to do the probability engine - this gets us all the possible clears and mines
                result = [];  // clear down any actions we found  trivially
                //return new EfficiencyHelper(board, witnesses, noFlagResult).process();
            } else {
                return result;
            }
            */
        }

        const pe = new ProbabilityEngine(board, witnesses, witnessed, squaresLeft, minesLeft, options);

        pe.process();

        writeToConsole("probability Engine took " + pe.duration + " milliseconds to complete");

        if (pe.finalSolutionCount == 0) {
            console.log("The board is in an illegal state");
            return result;
        }

        // if the tiles off the edge are definitely safe then clear them all
        let offEdgeAllSafe = false;
        if (pe.offEdgeProbability == 1) {
            const edgeSet = new Set();  // build a set containing all the on edge tiles
            for (let i = 0; i < witnessed.length; i++) {
                edgeSet.add(witnessed[i].index);
            }
            // any tiles not on the edge can be cleared
            for (let i = 0; i < allCoveredTiles.length; i++) {
                const tile = allCoveredTiles[i];
                if (!edgeSet.has(tile.index)) {
                    result.push(new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR));
                }
            }

            if (result.length > 0) {
                writeToConsole("The Probability Engine has determined all off edge tiles must be safe");
                offEdgeAllSafe = true;
                //console.log("The solver has determined all off edge tiles must be safe");
                //return result;
            }

        } else if (pe.offEdgeProbability == 0 && pe.fullAnalysis) {  
            writeToConsole("The Probability Engine has determined all off edge tiles must be mines");
            const edgeSet = new Set();  // build a set containing all the on edge tiles
            for (let i = 0; i < witnessed.length; i++) {
                edgeSet.add(witnessed[i].index);
            }
            // any tiles not on the edge are a mine
            for (let i = 0; i < allCoveredTiles.length; i++) {
                const tile = allCoveredTiles[i];
                if (!edgeSet.has(tile.index) && !tile.isFlagged()) {
                    pe.minesFound.push(tile)
                    //tile.setFoundBomb();
                }
            }
        }

        // If we have a full analysis then set the probabilities on the tile tooltips
        if (pe.fullAnalysis) {

             // Set the probability for each tile on the edge 
            for (let i = 0; i < pe.boxes.length; i++) {
                for (let j = 0; j < pe.boxes[i].tiles.length; j++) {
                    pe.boxes[i].tiles[j].setProbability(pe.boxProb[i]);
                }
            }

            // set all off edge probabilities
            for (let i = 0; i < board.tiles.length; i++) {

                const tile = board.getTile(i);

                if (tile.isSolverFoundBomb()) {
                    if (!tile.isFlagged()) {
                        tile.setProbability(0);
                    }
                } else if (tile.isCovered() && !tile.onEdge) {
                    tile.setProbability(pe.offEdgeProbability);
                }
            }
        }


        // have we found any local clears which we can use or everything off the edge is safe
        if (pe.localClears.length > 0 || pe.minesFound.length > 0 || offEdgeAllSafe) {
            for (let tile of pe.localClears) {   // place each local clear into an action
                tile.setProbability(1);
                const action = new Action(tile.getX(), tile.getY(), 1, ACTION_CLEAR);
                result.push(action);
            }

            for (let tile of pe.minesFound) {   // place each found flag
                tile.setProbability(0);
                tile.setFoundBomb();
                //if (options.playStyle == PLAY_STYLE_FLAGS) {
                    const action = new Action(tile.getX(), tile.getY(), 0, ACTION_FLAG);
                    result.push(action);
                //}
            }

            console.log("The probability engine has found " + pe.localClears.length + " safe clears and " + pe.minesFound.length + " mines");
            return new EfficiencyHelper(board, witnesses, witnessed, result, options.playStyle, pe).process();
        } 


        // this is part of the no-guessing board creation logic - wip
        if (pe.bestProbability < 1 && !options.advancedGuessing) {
            if (pe.bestOnEdgeProbability >= pe.offEdgeProbability) {
                result.push(pe.getBestCandidates(1));  // get best options
            } else {
                writeToConsole("Off edge is best, off edge prob = " + pe.offEdgeProbability + ", on edge prob = " + pe.bestOnEdgeProbability, true);
                const bestGuessTile = offEdgeGuess(board, witnessed);
                result.push(new Action(bestGuessTile.getX(), bestGuessTile.getY(), pe.offEdgeProbability), ACTION_CLEAR);
            }

            // find some witnesses which can be adjusted to remove the guessing
            findBalancingCorrections(pe);

            return result;
        }

        /*
        // if we don't have a certain guess then look for ...
        //let ltr;
        if (pe.bestOnEdgeProbability != 1 && minesLeft > 1) {

            // See if there are any unavoidable 2 tile 50/50 guesses 
            const unavoidable5050a = pe.checkForUnavoidable5050();
            if (unavoidable5050a != null) {
                result.push(new Action(unavoidable5050a.getX(), unavoidable5050a.getY(), unavoidable5050a.probability, ACTION_CLEAR));
                console.log(unavoidable5050a.asText() + " is an unavoidable 50/50 guess." + formatSolutions(pe.finalSolutionsCount));
                return addDeadTiles(result, pe.getDeadTiles());
            }

            // look for any 50/50 or safe guesses 
            //const unavoidable5050b = new FiftyFiftyHelper(board, pe.minesFound, options, pe.getDeadTiles(), witnessed, minesLeft).process();

            //ltr = new LongTermRiskHelper(board, pe, minesLeft, options);
            //const unavoidable5050b = ltr.findInfluence();
            //if (unavoidable5050b != null) {
            //    result.push(new Action(unavoidable5050b.getX(), unavoidable5050b.getY(), unavoidable5050b.probability, ACTION_CLEAR));
            //   console.log(unavoidable5050b.asText() + " is an unavoidable 50/50 guess, or safe." + formatSolutions(pe.finalSolutionsCount));
            //    return addDeadTiles(result, pe.getDeadTiles());
            //}
        }
        */

        // if we have an isolated edge process that
        if (pe.bestProbability < 1 && pe.isolatedEdgeBruteForce != null) {

            const solutionCount = pe.isolatedEdgeBruteForce.crunch();

            writeToConsole("Solutions found by brute force for isolated edge " + solutionCount);

            const bfda = new BruteForceAnalysis(pe.isolatedEdgeBruteForce.allSolutions, pe.isolatedEdgeBruteForce.iterator.tiles, 1000, options.verbose);  // the tiles and the solutions need to be in sync

            await bfda.process();

            // if the brute force deep analysis completed then use the results
            if (bfda.completed) {
                // if they aren't all dead then send the best guess
                if (!bfda.allTilesDead()) {
                    const nextmove = bfda.getNextMove();
                    result.push(nextmove);

                    deadTiles = bfda.deadTiles;
                    var winChanceText = (bfda.winChance * 100).toFixed(2);
                    console.log("The solver has calculated the best move has a " + winChanceText + "% chance to solve the isolated edge." + formatSolutions(pe.finalSolutionsCount));

                } else {
                    console.log("The solver has calculated that all the tiles on the isolated edge are dead." + formatSolutions(pe.finalSolutionsCount));
                    deadTiles = bfda.deadTiles;   // all the tiles are dead
                }

                return addDeadTiles(result, deadTiles);
            }

        }

        // if we are having to guess and there are less then BFDA_THRESHOLD solutions use the brute force deep analysis...
        let bfdaThreshold;
        bfdaThreshold = PLAY_BFDA_THRESHOLD;

        let partialBFDA = null;
        if (pe.bestProbability < 1 && pe.finalSolutionsCount < bfdaThreshold) {

            console.log("The solver is starting brute force deep analysis on " + pe.finalSolutionsCount + " solutions");
            await sleep(1);

            pe.generateIndependentWitnesses();

            const iterator = new WitnessWebIterator(pe, allCoveredTiles, -1);

            let bfdaCompleted = false;
            let bfda
            if (iterator.cycles <= BRUTE_FORCE_CYCLES_THRESHOLD) {
                const bruteForce = new Cruncher(board, iterator);

                const solutionCount = bruteForce.crunch();

                writeToConsole("Solutions found by brute force " + solutionCount + " after " + iterator.getIterations() + " cycles");

                bfda = new BruteForceAnalysis(bruteForce.allSolutions, iterator.tiles, 1000, options.verbose);  // the tiles and the solutions need to be in sync

                await bfda.process();

                bfdaCompleted = bfda.completed;
            } else {
                writeToConsole("Brute Force requires too many cycles - skipping BFDA: " + iterator.cycles);
            }


            // if the brute force deep analysis completed then use the results
            if (bfdaCompleted) {
                // if they aren't all dead then send the best guess
                if (!bfda.allTilesDead()) {
                    const nextmove = bfda.getNextMove();
                    result.push(nextmove);

                    deadTiles = bfda.deadTiles;
                    const winChanceText = (bfda.winChance * 100).toFixed(2);
                    console.log("The solver has calculated the best move has a " + winChanceText + "% chance to win the game." + formatSolutions(pe.finalSolutionsCount));

                } else {
                    console.log("The solver has calculated that all the remaining tiles are dead." + formatSolutions(pe.finalSolutionsCount));
                    deadTiles = allCoveredTiles;   // all the tiles are dead
                }

                return addDeadTiles(result, deadTiles);
            } else {
                deadTiles = pe.getDeadTiles();  // use the dead tiles from the probability engine
                partialBFDA = bfda;
            }

        } else {
            deadTiles = pe.getDeadTiles();  // use the dead tiles from the probability engine
        }

        // if we don't have a certain guess and we have too many solutions for brute force then look for ...
        let ltr;
        if (pe.bestOnEdgeProbability != 1 && minesLeft > 1) {

            // See if there are any unavoidable 2 tile 50/50 guesses 
            const unavoidable5050a = pe.checkForUnavoidable5050();
            if (unavoidable5050a != null) {
                result.push(new Action(unavoidable5050a.getX(), unavoidable5050a.getY(), unavoidable5050a.probability, ACTION_CLEAR));
                console.log(unavoidable5050a.asText() + " is an unavoidable 50/50 guess." + formatSolutions(pe.finalSolutionsCount));
                return addDeadTiles(result, pe.getDeadTiles());
            }

            // look for any 50/50 or safe guesses - old method
            //const unavoidable5050b = new FiftyFiftyHelper(board, pe.minesFound, options, pe.getDeadTiles(), witnessed, minesLeft).process();

            ltr = new LongTermRiskHelper(board, pe, minesLeft, options);
            const unavoidable5050b = ltr.findInfluence();
            if (unavoidable5050b != null) {
                result.push(new Action(unavoidable5050b.getX(), unavoidable5050b.getY(), unavoidable5050b.probability, ACTION_CLEAR));
               console.log(unavoidable5050b.asText() + " is an unavoidable 50/50 guess, or safe." + formatSolutions(pe.finalSolutionsCount));
                return addDeadTiles(result, pe.getDeadTiles());
            }
        }

        /*
        // calculate 50/50 influence and check for a pseudo-50/50
        let ltr;
        if (pe.bestOnEdgeProbability != 1 && minesLeft > 1) {

            ltr = new LongTermRiskHelper(board, pe, minesLeft, options);
            const unavoidable5050b = ltr.findInfluence();
            if (unavoidable5050b != null) {
                result.push(new Action(unavoidable5050b.getX(), unavoidable5050b.getY(), unavoidable5050b.probability, ACTION_CLEAR));
               console.log(unavoidable5050b.asText() + " is an unavoidable 50/50 guess, or safe." + formatSolutions(pe.finalSolutionsCount));
                return addDeadTiles(result, pe.getDeadTiles());
            }
        }
        */

        // ... otherwise we will use the probability engines results

        result.push(...pe.getBestCandidates(HARD_CUT_OFF));  // get best options within this ratio of the best value

        // if the off edge tiles are within tolerance then add them to the candidates to consider as long as we don't have certain clears
        if (pe.bestOnEdgeProbability != 1 && pe.offEdgeProbability > pe.bestOnEdgeProbability * OFF_EDGE_THRESHOLD) {
            result.push(...getOffEdgeCandidates(board, pe, witnesses, allCoveredTiles));
            result.sort(function (a, b) { return b.prob - a.prob });
        }

        // if we have some good guesses on the edge
        if (result.length > 0) {
            for (let i = 0; i < deadTiles.length; i++) {
                const tile = deadTiles[i];

                writeToConsole("Tile " + tile.asText() + " is dead");
                for (let j = 0; j < result.length; j++) {
                    if (result[j].x == tile.x && result[j].y == tile.y) {
                        result[j].dead = true;
                        //found = true;
                        break;
                    }
                }
            }

            if (pe.bestProbability == 1) {
                console.log("The solver has found some certain moves using the probability engine." + formatSolutions(pe.finalSolutionsCount));

                 // identify where the bombs are
                for (let tile of pe.minesFound) {
                    tile.setFoundBomb();
                    if (options.playStyle == PLAY_STYLE_FLAGS) {
                        const action = new Action(tile.getX(), tile.getY(), 0, ACTION_FLAG);
                        result.push(action);
                    }
                }
 
                result = new EfficiencyHelper(board, witnesses, witnessed, result, options.playStyle, pe).process();
            } else {
                console.log("The solver has found the best guess on the edge using the probability engine." + formatSolutions(pe.finalSolutionsCount));
                if (pe.duration < 50) {  // if the probability engine didn't take long then use some tie-break logic
                    result = tieBreak(pe, result, partialBFDA, ltr);
                }
            }

        } else {  // otherwise look for a guess with the least number of adjacent covered tiles (hunting zeros)
            const bestGuessTile = offEdgeGuess(board, witnessed);

            result.push(new Action(bestGuessTile.getX(), bestGuessTile.getY(), pe.offEdgeProbability), ACTION_CLEAR);

            console.log("The solver has decided the best guess is off the edge." + formatSolutions(pe.finalSolutionsCount));

        }

        return addDeadTiles(result, pe.getDeadTiles());;

    }

    // used to add the dead tiles to the results
    function addDeadTiles(result, deadTiles) {

        // identify the dead tiles
        for (let tile of deadTiles) {   // show all dead tiles 
            if (tile.probability != 0) {
                const action = new Action(tile.getX(), tile.getY(), tile.probability);
                action.dead = true;
                result.push(action);
            }
        }

        return result;

    }

    function tieBreak(pe, actions, bfda, ltr) {

        const start = Date.now();

        writeToConsole("Long term risks ==>");

        const alreadyIncluded = new Set();
        for (let action of actions) {
            alreadyIncluded.add(board.getTileXY(action.x, action.y));
        }

        const extraTiles = ltr.getInfluencedTiles(pe.bestProbability * 0.9);
        for (let tile of extraTiles) {
            if (alreadyIncluded.has(tile)) {
                //writeToConsole(tile.asText() + " is already in the list of candidates to be analysed");
            } else {
                alreadyIncluded.add(tile);
                actions.push(new Action(tile.getX(), tile.getY(), pe.getProbability(tile), ACTION_CLEAR));
                writeToConsole(tile.asText() + " added to the list of candidates to be analysed");
            }
        }
        writeToConsole("<==");

        let best;
        for (let action of actions) {

            if (action.action == ACTION_FLAG) { // ignore the action if it is a flagging request
                continue;
            }

            //fullAnalysis(pe, board, action, best);  // updates variables in the Action class

            secondarySafetyAnalysis(pe, board, action, best, ltr) // updates variables in the Action class

            if (best == null || best.weight < action.weight) {
                best = action;
            }

        }

        if (USE_HIGH_DENSITY_STRATEGY && board.isHighDensity() ) {
            writeToConsole("Board is high density prioritise minimising solutions space");
            actions.sort(function (a, b) {

                let c = b.prob - a.prob;
                if (c != 0) {
                    return c;
                } else if (a.maxSolutions > b.maxSolutions) {
                    return 1;
                } else if (a.maxSolutions < b.maxSolutions) {
                    return -1;
                } else {
                    return b.weight - a.weight;
                }

            });
        } else {
            actions.sort(function (a, b) {

                let c = b.weight - a.weight;
                if (c != 0) {
                    return c;
                } else {
                    return b.expectedClears - a.expectedClears;
                }

            });
        }

        if (bfda != null && actions.length > 0) {
            const better = bfda.checkForBetterMove(actions[0]);
            if (better != null) {
                const betterAction = new Action(better.x, better.y, better.probability, ACTION_CLEAR);
                writeToConsole("Replacing " + actions[0].asText() + " with " + betterAction.asText() + " because it is better from partial BFDA");
                actions = [betterAction];
            }
        }

        findAlternativeMove(actions);

        writeToConsole("Solver recommends (" + actions[0].x + "," + actions[0].y + ")");

        writeToConsole("Best Guess analysis took " + (Date.now() - start) + " milliseconds to complete");

        return actions;

    }

    // find a move which 1) is safer than the move given and 2) when move is safe ==> the alternative is safe
    function findAlternativeMove(actions) {

        const action = actions[0]  // the current best

        // if one of the common boxes contains a tile which has already been processed then the current tile is redundant
        for (let i = 1; i < actions.length; i++) {

            const alt = actions[i];

            if (alt.prob - action.prob > 0.001) {  // the alternative move is at least a bit safe than the current move
                for (let tile of action.commonClears) {  // see if the move is in the list of common safe tiles
                    if (alt.x == tile.x && alt.y == tile.y) {
                        writeToConsole("Replacing " + action.asText() + " with " + alt.asText() + " because it dominates");

                        // switch the alternative action with the best
                        actions[0] = alt;
                        actions[i] = action;

                        return;
                    }
                }
            }
        }

        // otherwise return the order
        return;

    }

    function trivial_actions(board, witnesses) {

        const result = new Map();

        for (let i = 0; i < witnesses.length; i++) {

            const tile = witnesses[i];

            const adjTiles = board.getAdjacent(tile);

            let flags = 0
            let covered = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    flags++;
                } else if (adjTile.isCovered()) {
                    covered++;
                }
            }

            // if the tile has the correct number of flags then the other adjacent tiles are clear
            if (flags == tile.getValue() && covered > 0) {
                for (let j = 0; j < adjTiles.length; j++) {
                    const adjTile = adjTiles[j];
                    if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                        adjTile.setProbability(1);  // definite clear
                        result.set(adjTile.index, new Action(adjTile.getX(), adjTile.getY(), 1, ACTION_CLEAR));
                    }
                }

            // if the tile has n remaining covered squares and needs n more flags then all the adjacent files are flags
            } else if (tile.getValue() == flags + covered && covered > 0) {
                for (let j = 0; j < adjTiles.length; j++) {
                    const adjTile = adjTiles[j];
                    if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) { // if covered, not already a known mine and isn't flagged
                        adjTile.setProbability(0);  // definite mine
                        adjTile.setFoundBomb();
                        //if (!adjTile.isFlagged()) {  // if not already flagged then flag it
                        result.set(adjTile.index, new Action(adjTile.getX(), adjTile.getY(), 0, ACTION_FLAG));
                        //}

                    }
                }
            } 

        }

        writeToConsole("Found " + result.size + " moves trivially");

        // send it back as an array
        return Array.from(result.values());

    }

    /**
     * Find the best guess off the edge when the probability engine doesn't give the best guess as on edge
     */
    function offEdgeGuess(board, witnessed) {

        const edgeSet = new Set();  // build a set containing all the on edge tiles
        for (let i = 0; i < witnessed.length; i++) {
            edgeSet.add(witnessed[i].index);
        }

        let bestGuess;
        let bestGuessCount = 9;

        for (let i = 0; i < board.tiles.length; i++) {
            const tile = board.getTile(i);

            // if we are an unrevealed square and we aren't on the edge
            // then store the location
            if (tile.isCovered() && !tile.isSolverFoundBomb() && !edgeSet.has(tile.index)) { // if the tile is covered and not on the edge

                const adjCovered = board.adjacentCoveredCount(tile);

                // if we only have isolated tiles then use this
                if (adjCovered == 0 && bestGuessCount == 9) {
                    writeToConsole(tile.asText() + " is surrounded by flags");
                    bestGuess = tile;
                }

                if (adjCovered > 0 && adjCovered < bestGuessCount) {
                    bestGuessCount = adjCovered;
                    bestGuess = tile;
                }
            }
        }

        if (bestGuess == null) {
            writeToConsole("Off edge guess has returned null!", true);
        }

        return bestGuess;

    }

    function getOffEdgeCandidates(board, pe, witnesses, allCoveredTiles) {

        writeToConsole("getting off edge candidates");

        const accepted = new Set();  // use a map to deduplicate the witnessed tiles

        // if there are only a small number of tiles off the edge then consider them all
        if (allCoveredTiles.length - pe.witnessed.length < 30) {
            for (let i = 0; i < allCoveredTiles.length; i++) {
                const workTile = allCoveredTiles[i];
                // if the tile  isn't on the edge
                if (!workTile.onEdge) {
                    accepted.add(workTile);
                }
            }

        } else {  // otherwise prioritise those most promising

            let offsets;
            if (board.isHighDensity()) {
                offsets = OFFSETS_ALL;
            } else {
                offsets = OFFSETS;
            }

            for (let i = 0; i < witnesses.length; i++) {

                const tile = witnesses[i];

                for (let j = 0; j < offsets.length; j++) {

                    const x1 = tile.x + offsets[j][0];
                    const y1 = tile.y + offsets[j][1];

                    if (x1 >= 0 && x1 < board.width && y1 >= 0 && y1 < board.height) {

                        const workTile = board.getTileXY(x1, y1);

                        //console.log(x1 + " " + y1 + " is within range, covered " + workTile.isCovered() + ", on Edge " + workTile.onEdge);
                        if (workTile.isCovered() && !workTile.isSolverFoundBomb() && !workTile.onEdge) {
                             accepted.add(workTile);
                        }
                    }

                }

            }

            for (let i = 0; i < allCoveredTiles.length; i++) {

                const workTile = allCoveredTiles[i];

                // if the tile isn't alrerady being analysed and isn't on the edge
                if (!accepted.has(workTile) && !workTile.onEdge) {

                    // see if it has a small number of free tiles around it
                    const adjCovered = board.adjacentCoveredCount(workTile);
                    if (adjCovered > 1 && adjCovered < 4) {
                        accepted.add(workTile);
                    }

                }

            }

        }

        const result = []

        // generate an array of tiles from the map
        for (let tile of accepted) {
            result.push(new Action(tile.x, tile.y, pe.offEdgeProbability, ACTION_CLEAR));
        }

        return result;

    }

    function fullAnalysis(pe, board, action, best) {

        const tile = board.getTileXY(action.x, action.y);
 
        const adjFlags = board.adjacentFoundMineCount(tile);
        const adjCovered = board.adjacentCoveredCount(tile);

        let progressSolutions = BigInt(0);
        let expectedClears = BigInt(0);
        let maxSolutions = BigInt(0);

        const probThisTile = action.prob;
        let probThisTileLeft = action.prob;  // this is used to calculate when we can prune this action

        // this is used to hold the tiles which are clears for all the possible values
        const commonClears = null;

        for (let value = adjFlags; value <= adjCovered + adjFlags; value++) {

            const progress = divideBigInt(solutions, pe.finalSolutionsCount, 6);
            const bonus = 1 + (progress + probThisTileLeft) * PROGRESS_CONTRIBUTION;
            const weight = probThisTile * bonus;

            if (best != null && weight < best.weight) {
                writeToConsole("(" + action.x + "," + action.y + ") is being pruned");
                action.weight = weight;
                action.pruned = true;

                tile.setCovered(true);   // make sure we recover the tile
                return;
            }

            tile.setValue(value);

            const work = countSolutions(board, null);

            if (work.finalSolutionsCount > 0) {  // if this is a valid board state
                if (commonClears == null) {
                    commonClears = work.getLocalClears();
                } else {
                    commonClears = andClearTiles(commonClears, work.getLocalClears());
                }

                const probThisTileValue = divideBigInt(work.finalSolutionsCount, pe.finalSolutionsCount, 6);
                probThisTileLeft = probThisTileLeft - probThisTileValue;

            }


            //totalSolutions = totalSolutions + work.finalSolutionsCount;
            if (work.clearCount > 0) {
                expectedClears = expectedClears + work.finalSolutionsCount * BigInt(work.clearCount);
                progressSolutions = progressSolutions + work.finalSolutionsCount;
            }

            if (work.finalSolutionsCount > maxSolutions) {
                maxSolutions = work.finalSolutionsCount;
            }

        }

        tile.setCovered(true);

        action.expectedClears = divideBigInt(expectedClears, pe.finalSolutionsCount, 6);

        const progress = divideBigInt(progressSolutions, pe.finalSolutionsCount, 6);

        action.progress = progress;

        action.weight = action.prob * (1 + progress * PROGRESS_CONTRIBUTION);
        action.maxSolutions = maxSolutions;
        action.commonClears = commonClears;

        tile.setProbability(action.prob, action.progress);

        writeToConsole(tile.asText() + ", progress = " + action.progress + ", weight = " + action.weight + ", expected clears = " + action.expectedClears + ", common clears = " + commonClears.length);

    }

    function countSolutions(board, notMines) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                continue;  // if the tile is a flag then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            let minesFound = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    minesFound++;
                } else if (adjTile.isCovered()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            // if a witness needs work (still has hidden adjacent tiles) or is broken then add it to the mix
            if (needsWork || minesFound > tile.getValue()) {
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        //console.log("tiles left = " + squaresLeft);
        //console.log("mines left = " + minesLeft);
        //console.log("Witnesses  = " + witnesses.length);
        //console.log("Witnessed  = " + witnessed.length);

        var solutionCounter = new SolutionCounter(board, witnesses, witnessed, squaresLeft, minesLeft);

        // let the solution counter know which tiles mustn't contain mines
        if (notMines != null) {
            for (let tile of notMines) {
                if (!solutionCounter.setMustBeEmpty(tile)) {
                    writeToConsole("Tile " + tile.asText() + " failed to set must be empty");
                }
            }
        }

        solutionCounter.process();

        return solutionCounter;

    }

    function secondarySafetyAnalysis(pe, board, action, best, ltr) {

        const progressContribution = 0.052;

        const tile = board.getTileXY(action.x, action.y);

        const safePe = runProbabilityEngine(board, [tile]);
        let linkedTilesCount = 0;
        let dominated = false;  // if tile 'a' being safe ==> tile 'b' & 'c' are safe and 'b' and 'c' are in the same box ==> 'b' is safer then 'a' 

        for (let box of safePe.emptyBoxes) {
            if (box.contains(tile)) { // if the tile is in this box then ignore it

            } else {
                if (box.tiles.length > 1) {
                    dominated = true;
                } else {
                    linkedTilesCount++;
                }
            }
        }

        writeToConsole("Tile " + tile.asText() + " has " + linkedTilesCount + " linked tiles and dominated=" + dominated);

        // a dominated tile doesn't need any further resolution
        if (dominated) {
            action.progress = action.prob;    // progress is total
            action.weight = action.prob * (1 + action.prob * progressContribution);
            action.maxSolutions = safePe.finalSolutionsCount;
            action.commonClears = safePe.localClears;

            tile.setProbability(action.prob, action.progress, action.progress);  // a dominated tile has 100% progress

            return;
        }

        const tileBox = pe.getBox(tile);
        let safetyTally;
        if (tileBox == null) {
            safetyTally = pe.finalSolutionsCount - pe.offEdgeMineTally;
        } else {
            safetyTally = pe.finalSolutionsCount - tileBox.mineTally;
        }

        const tileInfluenceTally = ltr.findTileInfluence(tile);
        //console.log("Safety Tally " + safetyTally + ", tileInfluenceTally " + tileInfluenceTally);

        //const fiftyFiftyInfluenceTally = safetyTally + tileInfluenceTally;
        const fiftyFiftyInfluence = 1 + divideBigInt(tileInfluenceTally, safetyTally, 6) * 0.9;

        let solutionsWithProgess = BigInt(0);
        let expectedClears = BigInt(0);
        let maxSolutions = BigInt(0);

        let secondarySafety = 0;
        let probThisTileLeft = action.prob;  // this is used to calculate when we can prune this action

        // this is used to hold the tiles which are clears for all the possible values
        var commonClears = null;

        const adjFlags = board.adjacentFoundMineCount(tile);
        const adjCovered = board.adjacentCoveredCount(tile);

        for (let value = adjFlags; value <= adjCovered + adjFlags; value++) {

            const progress = divideBigInt(solutionsWithProgess, pe.finalSolutionsCount, 6);
            const bonus = 1 + (progress + probThisTileLeft) * progressContribution;
            const weight = (secondarySafety + probThisTileLeft * fiftyFiftyInfluence) * bonus;

            if (best != null && weight < best.weight) {
                writeToConsole("Tile (" + action.x + "," + action.y + ") is being pruned,  50/50 influence = " + fiftyFiftyInfluence + ", max score possible is " + weight);
                action.weight = weight;
                action.pruned = true;

                tile.setCovered(true);   // make sure we recover the tile
                return;
            }

            tile.setValue(value);

            const work = runProbabilityEngine(board, null);

            if (work.finalSolutionsCount > 0) {  // if this is a valid board state
                if (commonClears == null) {
                    commonClears = work.localClears;
                } else {
                    commonClears = andClearTiles(commonClears, work.localClears);
                }

                //const longTermSafety = ltr.getLongTermSafety(tile, work);

                const probThisTileValue = divideBigInt(work.finalSolutionsCount, pe.finalSolutionsCount, 6);
                secondarySafety = secondarySafety + probThisTileValue * work.bestLivingProbability * fiftyFiftyInfluence;

                writeToConsole("Tile " + tile.asText() + " with value " + value + " has probability " + probThisTileValue + ", next guess safety " + work.bestLivingProbability + ", clears " + work.clearCount);

                probThisTileLeft = probThisTileLeft - probThisTileValue;
             }

            //totalSolutions = totalSolutions + work.finalSolutionsCount;
            if (work.clearCount > 0) {
                expectedClears = expectedClears + work.finalSolutionsCount * BigInt(work.clearCount);

                if (work.clearCount > linkedTilesCount) {  // this is intended to penalise tiles which are linked to other tiles. Otherwise 2 tiles give each other all progress.
                    solutionsWithProgess = solutionsWithProgess + work.finalSolutionsCount;
                }
            }

            if (work.finalSolutionsCount > maxSolutions) {
                maxSolutions = work.finalSolutionsCount;
            }

        }

        tile.setCovered(true);

        action.expectedClears = divideBigInt(expectedClears, pe.finalSolutionsCount, 6);

        const progress = divideBigInt(solutionsWithProgess, pe.finalSolutionsCount, 6);

        action.progress = progress;

        action.weight = secondarySafety * (1 + progress * progressContribution);
        action.maxSolutions = maxSolutions;
        action.commonClears = commonClears;

        const realSecondarySafety = (secondarySafety / fiftyFiftyInfluence).toFixed(6);  // remove the 50/50 influence to get back to the real secondary safety

        tile.setProbability(action.prob, action.progress, realSecondarySafety);

        writeToConsole("Tile " + tile.asText() + ", secondary safety = " + realSecondarySafety + ",  progress = " + action.progress + ", 50/50 influence = " + fiftyFiftyInfluence
            + ", expected clears = " + action.expectedClears + ", always clear = " + commonClears.length + ", final score = " + action.weight);

    }

    function runProbabilityEngine(board, notMines) {

        // find all the tiles which are revealed and have un-revealed / un-flagged adjacent squares
        const allCoveredTiles = [];
        const witnesses = [];
        const witnessed = [];

        let minesLeft = board.num_bombs;
        let squaresLeft = 0;

        const work = new Set();  // use a map to deduplicate the witnessed tiles

        for (let i = 0; i < board.tiles.length; i++) {

            const tile = board.getTile(i);

            if (tile.isSolverFoundBomb()) {
                minesLeft--;
                continue;  // if the tile is a flag then nothing to consider
            } else if (tile.isCovered()) {
                squaresLeft++;
                allCoveredTiles.push(tile);
                continue;  // if the tile hasn't been revealed yet then nothing to consider
            }

            const adjTiles = board.getAdjacent(tile);

            let needsWork = false;
            let minesFound = 0;
            for (let j = 0; j < adjTiles.length; j++) {
                const adjTile = adjTiles[j];
                if (adjTile.isSolverFoundBomb()) {
                    minesFound++;
                } else if (adjTile.isCovered()) {
                    needsWork = true;
                    work.add(adjTile.index);
                }
            }

            // if a witness needs work (still has hidden adjacent tiles) or is broken then add it to the mix
            if (needsWork || minesFound > tile.getValue()) {
                witnesses.push(tile);
            }

        }

        // generate an array of tiles from the map
        for (let index of work) {
            const tile = board.getTile(index);
            tile.setOnEdge(true);
            witnessed.push(tile);
        }

        //console.log("tiles left = " + squaresLeft);
        //console.log("mines left = " + minesLeft);
        //console.log("Witnesses  = " + witnesses.length);
        //console.log("Witnessed  = " + witnessed.length);

        const options = {};
        options.verbose = false;
        options.playStyle = PLAY_STYLE_EFFICIENCY;  // this forces the pe to do a complete run even if local clears are found

        const pe = new ProbabilityEngine(board, witnesses, witnessed, squaresLeft, minesLeft, options);

        // let the solution counter know which tiles mustn't contain mines
        if (notMines != null) {
            for (let tile of notMines) {
                pe.setMustBeEmpty(tile);
            }
        }

        pe.process();

        return pe;

    }

    function andClearTiles(tiles1, tiles2) {

        if (tiles1.length == 0) {
            return tiles1;
        }
        if (tiles2.length == 0) {
            return tiles2;
        }

        const result = [];
        for (let tile1 of tiles1) {
            for (let tile2 of tiles2) {
                if (tile2.isEqual(tile1)) {
                    result.push(tile1);
                    break;
                }
            }
        }

        return result;

    }

    // when looking to fix a board to be no-guess, look for witnesses which can have mines added or removed to make then no longer guesses
    function findBalancingCorrections(pe) {

        const adders = [...pe.prunedWitnesses];
        adders.sort((a, b) => adderSort(a, b));

        /*
        for (let i = 0; i < adders.length; i++) {
            const boxWitness = adders[i];
            const minesToFind = boxWitness.minesToFind;
            const spacesLeft = boxWitness.tiles.length;

            console.log(boxWitness.tile.asText() + " length " + boxWitness.tiles.length + ", add " + (spacesLeft - minesToFind) + ", remove " + minesToFind);
        }
        */

        let balanced = false;

        for (let i = 0; i < adders.length; i++) {
            const boxWitness = adders[i];

            if (findBalance(boxWitness, adders)) {
                writeToConsole("*** Balanced ***", true);
                balanced = true;
                break;
            }

        }

        if (!balanced) {
            writeToConsole("*** NOT Balanced ***", true);
            fillerTiles = [];
        }

       
    }

    function findBalance(boxWitness, adders) {

        // these are the adjustments which will all the tile to be trivially solved
        const toRemove = boxWitness.minesToFind;
        const toAdd = boxWitness.tiles.length - toRemove;

        writeToConsole("trying to balance " + boxWitness.tile.asText() + " to Remove=" + toRemove + ", or to Add=" + toAdd, true);

        top: for (let balanceBox of adders) {
            if (balanceBox.tile.isEqual(boxWitness.tile)) {
                continue;
            }

            // ensure the balancing witness doesn't overlap with this one
            for (let adjTile of board.getAdjacent(balanceBox.tile)) {
                if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                    if (adjTile.isAdjacent(boxWitness.tile)) {
                        continue top;
                    }
                }
            }

            const toRemove1 = balanceBox.minesToFind;
            const toAdd1 = balanceBox.tiles.length - toRemove1;

            if (toAdd1 == toRemove) {
                writeToConsole("found balance " + balanceBox.tile.asText() + " to Add=" + toAdd1, true);
                addFillings(boxWitness, false); // remove from here
                addFillings(balanceBox, true); // add to here
                return true;
            }

            if (toRemove1 == toAdd) {
                writeToConsole("found balance " + balanceBox.tile.asText() + " to Remove=" + toRemove1, true);
                addFillings(boxWitness, true); // add to here
                addFillings(balanceBox, false); // remove from here
                return true;
            }

        }

        return false;

    }

    /*
    function collisionSafe(tile) {

        for (var adjTile of board.getAdjacent(tile)) {
            if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                for (var filler of fillerTiles) {
                    if (filler.x == adjTile.x && filler.y == adjTile.y) {
                        return false;
                    }
                }
            }
        }

        return true;
    }
    */

    function adderSort(a, b) {

        // tiels with smallest area first
        let c = a.tiles.length - b.tiles.length;

        // then by the number of mines to find
        if (c == 0) {
            c = a.minesToFind - b.minesToFind;
        }

        return c;
    }

    function addFillings(boxWitness, fill) {

        for (let adjTile of boxWitness.tiles) {
            if (adjTile.isCovered() && !adjTile.isSolverFoundBomb()) {
                const filler = new Filling(adjTile.index, adjTile.x, adjTile.y, fill);
                fillerTiles.push(filler);
                //writeToConsole(filler.asText(), true);
            }
        }


    }

    function writeToConsole(text, always) {

        if (always == null) {
            always = false;
        }

        if (options.verbose || always) {
            console.log(text);
        }

    }

}

// shared functions

function formatSolutions(count) {

    if (count > maxSolutionsDisplay) {
        let work = count;
        let index = 3;
        let power = 0;
        while (work > power10n[index * 2]) {
            work = work / power10n[index];
            power = power + index;
        }

        const value = divideBigInt(work, power10n[index], 3);
        power = power + 3;

        return " Approximately " + value + " * 10<sup>" + power + "</sup> possible solutions remain.";
    } else {
        return " " + count.toLocaleString() + " possible solutions remain.";
    }

}

function combination(mines, squares) {

    return BINOMIAL.generate(mines, squares);

}

function divideBigInt(numerator, denominator, dp) {

    const work = numerator * power10n[dp] / denominator;

    const result = Number(work) / power10[dp];

    return result;
}

// location with probability of being safe
class Filling {
    constructor(index, x, y, fill) {
        this.index = index;
        this.x = x;
        this.y = y;
        this.fill = fill;  // mines left to find
    }

    asText() {

        return "(" + this.x + "," + this.y + ") Fill " + this.fill;

    }

}

function toggleShowHints(value) {
    showHints = value;
}

function changePlayStyle(value) {
    playStyle = value;
}

function changeOverlay(value) {
    overlay = value;
}

async function startup() {

    BINOMIAL = new Binomial(50000, 200);

    // canvas.addEventListener('mousemove', (event) => followCursor(event));

    // initialise the solver
    await solver();

    console.log('Started Minesweeper Helper');
}

function resetBoard() {
    let boardData = getBoard();

    newBoardFromString(boardData);
}

function getBoard() {
    let width = -1;
    let height = -1;
    let mines = -1;

    let currentLevel = document.getElementsByClassName('level-select-link active')[0];

    if (typeof currentLevel === 'undefined') {
        let numCols = 1000;
        let numRows = 1000;
        let colsAdjusted = false;
        let breakLoop = false;
        let data = '';
        let i;
        for (i = 0; i < numRows; i++) {
            if (breakLoop) {
                break;
            }
            for (let j = 0; j < numCols; j++) {
                let cell = document.getElementById(`cell_${j}_${i}`);
                if (typeof cell === 'undefined' || cell === null) {
                    if (colsAdjusted) {
                        breakLoop = true;
                        break;
                    }
                    numCols = j;
                    colsAdjusted = true;
                    break;
                }
                let cellStatus = 'H';
                if (cell.className.includes('hd_flag')) {
                    cellStatus = 'F';
                } else if (cell.className.includes('hd_type')) {
                    cellStatus = parseInt(cell.className.slice(-1));
                }
                data = data + cellStatus;
            }
            data = data + '\n';
        }
        let hundreds = document.getElementById('top_area_mines_100');
        let tens = document.getElementById('top_area_mines_10');
        let ones = document.getElementById('top_area_mines_1');
        let minesStr = '';
        let listNums = [hundreds, tens, ones];
        for (let num of listNums) {
            if (num.classList.contains('hd_top-area-num0')) {
                minesStr += '0';
            } else if (num.classList.contains('hd_top-area-num1')) {
                minesStr += '1';
            } else if (num.classList.contains('hd_top-area-num2')) {
                minesStr += '2';
            } else if (num.classList.contains('hd_top-area-num3')) {
                minesStr += '3';
            } else if (num.classList.contains('hd_top-area-num4')) {
                minesStr += '4';
            } else if (num.classList.contains('hd_top-area-num5')) {
                minesStr += '5';
            } else if (num.classList.contains('hd_top-area-num6')) {
                minesStr += '6';
            } else if (num.classList.contains('hd_top-area-num7')) {
                minesStr += '7';
            } else if (num.classList.contains('hd_top-area-num8')) {
                minesStr += '8';
            } else if (num.classList.contains('hd_top-area-num9')) {
                minesStr += '9';
            }
        }
        mines = parseInt(minesStr, 10);
        let header = `${numCols}x${i-1}x${mines}\n`;
        return header + data;
    }

    switch (currentLevel.textContent) {
        case 'Easy':
        case 'Beginner':
            width = 9;
            height = 9;
            mines = 10;
            break;
        case 'Medium':
        case 'Intermediate':
            width = 16;
            height = 16;
            mines = 40;
            break;
        case 'Hard':
        case 'Expert':
            width = 30;
            height = 16;
            mines = 99;
            break;
        case 'Evil':
            width = 30;
            height = 20;
            mines = 130;
            break;
        default:
            break;
    }

    if (width === -1) {
        // custom mode
        width = document.getElementById('custom_width').value;
        height = document.getElementById('custom_height').value;
        mines = document.getElementById('custom_mines').value;
    }

    let data = `${width}x${height}x${mines}\n`;
    for (let i = 0; i < height; i++) {
        for (let j = 0; j < width; j++) {
            let cell = document.getElementById(`cell_${j}_${i}`);
            let cellStatus = 'H';
            if (cell.className.includes('hd_flag')) {
                cellStatus = 'F';
            } else if (cell.className.includes('hd_type')) {
                cellStatus = parseInt(cell.className.slice(-1));
            }
            data = data + cellStatus;
        }
        data = data + '\n';
    }
    return data;
}

// stuff to do when we click on the board
function on_click(event, x, y) {

    if (!analysing) {
        // only check clicks if board is being analysed
        return;
    }

    //console.log("Click event at X=" + event.offsetX + ", Y=" + event.offsetY);

    let faceElement = document.getElementById('top_area_face');
    if (faceElement.className.includes('face-lose')) {
        // game is over
        analysing = false;
        // window.requestAnimationFrame(() => renderHints([], []));
        return;
    }

    if (canvasLocked) {
        console.log("The canvas is logically locked - this happens while the previous click is being processed");
        return;
    }

    const button = event.which

    const tile = board.getTileXY(x, y);

    // left mouse button
    if (button == 1 && tile.isFlagged()) { 
        // no point clicking on an tile with a flag on it
        console.log("Tile has a flag on it - no action to take");
        return;
    }

    // for all other cases we need to read new board
    resetBoard();
    // analyse new board
    doAnalysis();
    
}

// download as MBF
// create a BLOB of the data, insert a URL to it into the download link
async function downloadAsMBF(e) {

    // create a download name based on the date/time
    const now = new Date();

    const filename = "Download" + now.toISOString() + ".mbf";

    downloadHyperlink.download = filename;

}

// render an array of tiles to the canvas
function renderHints(hints, otherActions) {

    if (hints == null) {
        return;
    }

    let firstGuess = 0;  // used to identify the first (best) guess, subsequent guesses are just for info 
    for (let i = 0; i < hints.length; i++) {

        const hint = hints[i];

        let cell = document.getElementById(`cell_${hint.x}_${hint.y}`);

        if (hint.action == ACTION_CHORD) {
            console.log(`safe: (${hint.x},${hint.y})`);
            cell.classList.add('hd_safe'); 
            cell.classList.remove('hd_unsafe');
            cell.classList.remove('hd_dead');
            cell.classList.remove('hd_efficient');
        } else if (hint.prob == 0) {   // mine
            console.log(`mine: (${hint.x},${hint.y})`);
            cell.classList.add('hd_unsafe');
            cell.classList.remove('hd_safe');
            cell.classList.remove('hd_dead');
            cell.classList.remove('hd_efficient'); 
        } else if (hint.prob == 1) {  // safe
            console.log(`safe: (${hint.x},${hint.y})`);
            cell.classList.add('hd_safe');
            cell.classList.remove('hd_unsafe');
            cell.classList.remove('hd_dead');
            cell.classList.remove('hd_efficient');
        } else if (hint.dead) {  // uncertain but dead
            console.log(`dead: (${hint.x},${hint.y})`);
            cell.classList.add('hd_dead');
            cell.classList.remove('hd_safe');
            cell.classList.remove('hd_unsafe');
            cell.classList.remove('hd_efficient'); 
        } else {  //uncertain
            console.log(`efficient: (${hint.x},${hint.y})`);
            cell.classList.add('hd_efficient');
            cell.classList.remove('hd_safe');
            cell.classList.remove('hd_unsafe');
            cell.classList.remove('hd_dead'); 
            if (firstGuess == 0) {
                firstGuess = 1;
            }
        }
        cell.classList.remove('hd_closed');

        // cell.style.color=cellColor;
        // cell.style.opacity = '0.5';

        // if (firstGuess == 1) {
        //     ctxHints.fillStyle = "#00FF00";
        //     ctxHints.fillRect((hint.x + 0.25) * TILE_SIZE, (hint.y + 0.25) * TILE_SIZE, 0.5 * TILE_SIZE, 0.5 * TILE_SIZE);
        //     firstGuess = 2;
        // }

    }

    // TODO(danielatk): fix this!
    // put percentage over the tile 
    if (overlay != "none") {
        let font = "14px serif";

        for (let tile of board.tiles) {
            if (tile.getHasHint() && tile.isCovered() && !tile.isFlagged() && tile.probability != null) {
                if (!showHints || (tile.probability != 1 && tile.probability != 0)) {  // show the percentage unless we've already colour coded it

                    let value;
                    if (overlay == "safety") {
                        value = tile.probability * 100;
                    } else {
                        value = (1 - tile.probability) * 100;
                    }

                    let value1;
                    if (value < 9.95) {
                        value1 = value.toFixed(1);
                    } else {
                        value1 = value.toFixed(0);
                    }

                    // const offsetX = (TILE_SIZE - ctxHints.measureText(value1).width) / 2;

                    // ctxHints.fillText(value1, tile.x * TILE_SIZE + offsetX, (tile.y + 0.7) * TILE_SIZE, TILE_SIZE);

                }
            }
        }
    }


    if (otherActions == null) {
        return;
    }

    // these are from the efficiency play style and are the known moves which haven't been made
    for (let action of otherActions) {
        let cell = document.getElementById(`cell_${action.x}_${action.y}`);
        if (action.action == ACTION_CLEAR) {
            cell.classList.add('hd_safe');
            cell.classList.remove('hd_unsafe');
            cell.classList.remove('hd_dead');
            cell.classList.remove('hd_efficient');
        } else {
            cell.classList.add('hd_unsafe');
            cell.classList.remove('hd_safe');
            cell.classList.remove('hd_dead');
            cell.classList.remove('hd_efficient');
        }
        cell.classList.remove('hd_closed');
    }

}

// render an array of tiles to the canvas
function renderTiles(tiles) {

    //console.log(tiles.length + " tiles to render");

    for (let i = 0; i < tiles.length; i++) {
        const tile = tiles[i];
        let tileType = HIDDEN;

        if (tile.isBomb()) {
            if (tile.exploded) {
                tileType = EXPLODED;
            } else {
                tileType = BOMB;
            }
 
        } else if (tile.isFlagged()) {
            if (tile.isBomb() == null || tile.isBomb()) {  // isBomb() is null when the game hasn't finished
                tileType = FLAGGED;
            } else {
                tileType = FLAGGED_WRONG;
            }

        } else if (tile.isCovered()) {
            tileType = HIDDEN;

        } else {
            tileType = tile.getValue();
        }
        draw(tile.x, tile.y, tileType);
    }


}

function newBoardFromString(data) {

    const lines = data.split('\n');
    const size = lines[0].split('x');

    if (size.length != 3) {
        console.log(`Header line is invalid: ${lines[0]}`);
        return;
    }

    const width = parseInt(size[0]);
    const height = parseInt(size[1]);
    const mines = parseInt(size[2]);

    console.log(`width: ${width}, height: ${height}, mines: ${mines}`);

    if (width < 1 || height < 1 || mines < 1) {
        console.log('Invalid dimensions for game');
        return;
    }

    if (lines.length < height + 1) {
        console.log(`Insufficient lines to hold the data: ${lines.length}`);
        return;
    }

    const newBoard = new Board(1, width, height, mines);

    for (let y = 0; y < height; y++) {
        const line = lines[y + 1];
        console.log(line);
        for (let x = 0; x < width; x++) {

            const char = line.charAt(x);
            const tile = newBoard.getTileXY(x, y);

            if (char == 'F') {
                tile.toggleFlag();
                newBoard.bombs_left--;
            } else if (char == '0') {
                tile.setValue(0);
            } else if (char == '1') {
                tile.setValue(1);
            } else if (char == '2') {
                tile.setValue(2);
            } else if (char == '3') {
                tile.setValue(3);
            } else if (char == '4') {
                tile.setValue(4);
            } else if (char == '5') {
                tile.setValue(5);
            } else if (char == '6') {
                tile.setValue(6);
            } else if (char == '7') {
                tile.setValue(7);
            } else if (char == '8') {
                tile.setValue(8);
            } else {
                tile.setCovered(true);
            }
        }
    }

    if (board === null || typeof board === 'undefined') {
        // setup tile listeners only if hasn't been done yet
        for (let i = 0; i < newBoard.height; i++) {
            for (let j = 0; j < newBoard.width; j++) {
                let cell = document.getElementById(`cell_${j}_${i}`);
                // cell.addEventListener('click', (event) => 
                //     on_click(event, j, i)
                // );
            }
        }

        // setup face listener only if hasn't been done yet
        // document.getElementById('top_area_face').addEventListener('click', (event) => 
        //     () => {
        //         analysing = false;
        //         window.requestAnimationFrame(() => renderHints([], []));
        //     }
                
        // );
    }


    board = newBoard;

    return newBoard;
}

async function sleep(msec) {
    return new Promise(resolve => setTimeout(resolve, msec));
}

async function doAnalysis() {

    analysing = true;

    if (canvasLocked) {
        console.log("Already analysing... request rejected");
        return;
    } else {
        console.log("Doing analysis");
        canvasLocked = true;
    }

    // put out a message and wait long enough for the ui to update
    console.log('Analysing...');

    // this will set all the obvious mines which makes the solution counter a lot more efficient on very large boards
    board.resetForAnalysis();
    board.findAutoMove();
 
    const solutionCounter = solver.countSolutions(board);

    if (solutionCounter.finalSolutionsCount != 0) {

         const options = {};
        if (playStyle == "flag") {
            options.playStyle = PLAY_STYLE_FLAGS;
        } else if (playStyle == "noflag") {
            options.playStyle = PLAY_STYLE_NOFLAGS;
        } else if (playStyle == "eff") {
            options.playStyle = PLAY_STYLE_EFFICIENCY;
        } else {
            options.playStyle = PLAY_STYLE_NOFLAGS_EFFICIENCY; 
        } 

        if (overlay != "none") {
            options.fullProbability = true;
        } else {
            options.fullProbability = false;
        }
 
        const solve = await solver(board, options);  // look for solutions
        const hints = solve.actions;

        justPressedAnalyse = true;

        // window.requestAnimationFrame(() => renderHints(hints, solve.other));
        // renderHints(hints, solve.other);
    } else {
        console.log("The board is in an invalid state");
        // window.requestAnimationFrame(() => renderHints([], []));
        // renderHints([], []);
    }

    // by delaying removing the logical lock we absorb any secondary clicking of the button / hot key
    setTimeout(function () { canvasLocked = false; }, 200);
}

// draw a tile to the canvas
function draw(x, y, tileType) {

    //console.log('Drawing image...');

    if (tileType == BOMB) {
        ctx.drawImage(images[0], x * TILE_SIZE, y * TILE_SIZE, TILE_SIZE, TILE_SIZE);  // before we draw the bomb depress the square
    }


    ctx.drawImage(images[tileType], x * TILE_SIZE, y * TILE_SIZE, TILE_SIZE, TILE_SIZE);

}

// have the tooltip follow the mouse
function followCursor(e) {

    // get the tile we're over
    const row = Math.floor(event.offsetY / TILE_SIZE);
    const col = Math.floor(event.offsetX / TILE_SIZE);
    hoverTile = board.getTileXY(col, row);

    // if not showing hints don't show tooltip
    if (!showHints && !justPressedAnalyse) {
        tooltip.innerText = "";
        return;
    }

    //console.log("Following cursor at X=" + e.offsetX + ", Y=" + e.offsetY);

    tooltip.style.left = (TILE_SIZE + e.clientX - 220) + 'px';
    tooltip.style.top = (e.clientY - TILE_SIZE * 1.5 - 70) + 'px';

    if (row >= board.height || row < 0 || col >= board.width || col < 0) {
        //console.log("outside of game boundaries!!");
        tooltip.innerText = "";
        tooltip.style.display = "none";
        return;
    } else {
        const tile = board.getTileXY(col, row);
        tooltip.innerText = tile.asText() + " " + tile.getHintText();
        tooltip.style.display = "inline-block";
    }

}