const puppeteer = require('puppeteer');
const fs = require('fs');

const args = process.argv.slice(2);

if (args.length === 0) {
    console.log('Please provide a game ID');
    return;
}

function arraysAreEqual(array1, array2) {
    if (array1.length !== array2.length) {
        return false;
    }

    for (let i = 0; i < array1.length; i++) {
        if (array1[i] !== array2[i]) {
            return false;
        }
    }

    return true;
}


(async () => {
    const browser = await puppeteer.launch({
        headless: false,
        args: [
            `--start-maximized`,
        ],
    });
    
    const page = await browser.newPage();
    
    function getCellId(cell) {
        const coordinates = cell.replace('(','').replace(')','').split(',');
        return `cell_${coordinates[0]}_${coordinates[1]}`;
    }

    let solverRecommendation;
    
    const clickedTiles = new Map();
    
    let safeTiles = [];
    let deadTiles = [];
    let efficientTiles = [];
    let mineTiles = [];

    page.on('console', (msg) => {
        if (msg.text().includes('safe: ')) {
            safeTiles.push(msg.text().replace('safe: ',''));
        } else if (msg.text().includes('mine: ')) {
            mineTiles.push(msg.text().replace('mine: ',''));
        } else if (msg.text().includes('dead: ')) {
            deadTiles.push(msg.text().replace('dead: ',''));
        } else if (msg.text().includes('efficient: ')) {
            efficientTiles.push(msg.text().replace('efficient: ',''));
        } else if (msg.text().includes('Solver recommends ')) {
            solverRecommendation = msg.text().replace('Solver recommends ','');
        }
    });

    await page.goto(`https://minesweeper.online/game/${args[0]}`);

    await page.waitForSelector('#top_area_face');

    const content = fs.readFileSync('combined.js', 'utf8');
    await page.evaluate(content);

    async function sleep(msec) {
        return new Promise(resolve => setTimeout(resolve, msec));
    }

    let lastSafeTiles = Array.from(safeTiles);
    let lastEfficientTiles = Array.from(efficientTiles);
    let lastMineTiles = Array.from(mineTiles);
    let lastDeadTiles = Array.from(deadTiles);

    const clickCycleState = {
        unchanged: "unchanged",
        changed: "changed",
    };

    // in milliseconds
    const pollingInterval = 100;
    const timeoutDuration = 5000;

    let tolerateNoTilesToSet = true;

    async function clickCycle(isFirst = false) {
        if (isFirst) {
            await sleep(1000);
        }

        let hasEnded = await page.evaluate(() => {
            const gameStatus = document.getElementById('top_area_face');
            const hasEnded = gameStatus.classList.contains('hd_top-area-face-lose')
                || gameStatus.classList.contains('hd_top-area-face-win');
            return hasEnded;
        });

        if (hasEnded) {
            return;
        }

        const startTime = Date.now();

        let changeState = clickCycleState.unchanged;

        let clickAlreadySet = false;

        while (true) {
            console.log(`\n`);
            await sleep(pollingInterval);

            if (Date.now() - startTime > timeoutDuration) {
                console.log('Timeout reached. Exiting clickCycle.');
                return;
            }

            const safeTilesTmp = Array.from(safeTiles);
            const efficientTilesTmp = Array.from(efficientTiles);
            const mineTilesTmp = Array.from(mineTiles);
            const deadTilesTmp = Array.from(deadTiles);

            const hasChanged = !arraysAreEqual(safeTilesTmp, lastSafeTiles) ||
                !arraysAreEqual(efficientTilesTmp, lastEfficientTiles) ||
                !arraysAreEqual(mineTilesTmp, lastMineTiles) ||
                !arraysAreEqual(deadTilesTmp, lastDeadTiles);

            if (changeState == clickCycleState.unchanged) {
                if (hasChanged) {
                    lastSafeTiles = Array.from(safeTilesTmp);
                    lastEfficientTiles = Array.from(efficientTilesTmp);
                    lastMineTiles = Array.from(mineTilesTmp);
                    lastDeadTiles = Array.from(deadTilesTmp);

                    changeState = clickCycleState.changed;
                } else {
                    clickAlreadySet = true;
                    break;
                }
                continue;
            }

            if (changeState == clickCycleState.changed) {
                if (hasChanged) {
                    lastSafeTiles = Array.from(safeTilesTmp);
                    lastEfficientTiles = Array.from(efficientTilesTmp);
                    lastMineTiles = Array.from(mineTilesTmp);
                    lastDeadTiles = Array.from(deadTilesTmp);

                    continue;
                }
                break;
            }
        }

        const safeTilesTmp = Array.from(safeTiles);
        const efficientTilesTmp = Array.from(efficientTiles);
        const mineTilesTmp = Array.from(mineTiles);
        const deadTilesTmp = Array.from(deadTiles);

        safeTiles.length = 0;
        efficientTiles.length = 0;
        mineTiles.length = 0;
        deadTiles.length = 0;

        let didClick = clickAlreadySet;

        if (clickAlreadySet) {
            const tileToSet = clickedTiles.keys().next().value;

            await page.click(`#${getCellId(tileToSet)}`);
        }

        if (!didClick) {
            // first check for safe tiles
            let tilesToSet = safeTilesTmp.filter((tile) => !clickedTiles.has(tile));
            didClick = tilesToSet.length;
            for (tile of tilesToSet) {
                clickedTiles.set(tile);
            }
    
            if (didClick) {
                for (let tile of tilesToSet) {
                    page.click(`#${getCellId(tile)}`);
                }
            }
        }

        if (!didClick) {
            // if no safe tiles try efficient tiles
            tilesToSet = efficientTilesTmp.filter((tile) => !clickedTiles.has(tile));
            didClick = tilesToSet.length;

            if (didClick) {
                let tileToSet;
                tileToSet = tilesToSet[0];
                clickedTiles.set(tileToSet);
                await page.click(`#${getCellId(tileToSet)}`);
            }
        }

        if (didClick) {
            tolerateNoTilesToSet = true;
        } else {
            if (!tolerateNoTilesToSet) {
                return;
            }

            const tileToSet = clickedTiles.keys().next().value;

            await page.click(`#${getCellId(tileToSet)}`);

            tolerateNoTilesToSet = false;
        }

        await page.evaluate(() => {
            window.resetBoard();
            window.doAnalysis();
        });

        clickCycle();
    }

    console.log('At start of index.js');

    await page.evaluate(async () => {
        await window.startup();
    
        document.getElementById('top_area_face').click();
    
        window.resetBoard();
        window.doAnalysis();
    });

    await clickCycle(true);

})();