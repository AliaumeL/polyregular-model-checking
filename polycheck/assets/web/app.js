

window.onload = () => {

    const inputForm     = document.getElementById('user-input');
    const codeAssets    = document.getElementById('code-assets');
    const codeInput     = document.getElementById('code');
    const preAsset      = document.getElementById('pre-assets');
    const preInput      = document.getElementById('pre');
    const postAsset     = document.getElementById('post-assets');
    const postInput     = document.getElementById('post');
    const output        = document.getElementById('output-view');
    const outputWarn    = document.getElementById('output-warn');
    const submitButton  = document.getElementById('submit');


    const codeAssetList = {};
    const formAssetList = {};
    const solversList   = [];

    const parseInputs = () => {
        fetch('/api/parse/', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify({ 
                program:  codeInput.value, 
                precond:  preInput.value,
                postcond: postInput.value,
            })
        })
        .then(res => res.json())
        .then(data => {
            outputWarn.innerHTML = '';
            if (data.parseErrProg) {
                codeInput.classList.add('error');
                const p = document.createElement('p');
                p.textContent = `Π — ${data.parseErrProg}`;
                outputWarn.appendChild(p);
            } else {
                codeInput.classList.remove('error');
            } 

            if (data.parseErrPre) {
                preInput.classList.add('error');
                const p = document.createElement('p');
                p.textContent = `Φ — ${data.parseErrPre}`;
                outputWarn.appendChild(p);
            } else {
                preInput.classList.remove('error');
            }

            if (data.parseErrPost) {
                postInput.classList.add('error');
                const p = document.createElement('p');
                p.textContent = `Ψ — ${data.parseErrPost}`;
                outputWarn.appendChild(p);
            } else {
                postInput.classList.remove('error');
            }

            if (!(data.parseErrProg || data.parseErrPre || data.parseErrPost)) {
                outputWarn.textContent = '👍 All inputs are valid and ready for verification!';
                outputWarn.classList.remove('error');
                outputWarn.classList.add('success');
                submitButton.disabled = false;
            } else {
                outputWarn.classList.remove('success');
                outputWarn.classList.add('error');
                submitButton.disabled = true;
            }

        })
        .catch(err => {
            console.error(err);
        });
    };
    
    /* prevent submission from inputForm, and register our own handler */
    inputForm.addEventListener('submit', (e) => {
        e.preventDefault();
        const program  = codeInput.value;
        const precond  = preInput.value;
        const postcond = postInput.value;

        output.textContent = '💭 Verifying...';

        output.innerHTML = '';
        const banner = document.createElement('p');
        const ul     = document.createElement('ul');
        banner.textContent = 'Verifying...';
        /* add hrule */
        output.appendChild(document.createElement('hr'));
        output.appendChild(ul);
        output.appendChild(document.createElement('hr'));
        output.appendChild(banner);
        
        const solverPromises = solversList.map(({ solverName, solverStatus }) => {
          if (solverStatus === "installed") {
            const li = document.createElement('li');
            ul.appendChild(li);
            li.textContent = `💭 Verifying with ${solverName}...`;
            return getSolverResult(solverName, program, precond, postcond)
                   .then(response => {
                        li.textContent = JSON.stringify(response);
                        const answer     = response.answer;
                        if (answer === 'Unsat') {
                            li.textContent = `✅ ${solverName}: OK!`;
                            li.classList.add('success');
                        } else if (answer === 'Sat') {
                            li.textContent = `❌ ${solverName}: NO!`;
                            li.classList.add('error');
                        } else if (answer === 'Unknown') {
                            li.textContent = `🤷 ${solverName}: ???`;
                            li.classList.add('neutral');
                        } else {
                            li.textContent = `🪲 ${solverName}: ${answer}`;
                        }
                   });
          }
        });

        Promise.all(solverPromises).then(() => {
           banner.textContent = '💯 Verification complete!';
        });
        

    });

    codeAssets.addEventListener('change', () => {
        codeInput.value = codeAssetList[codeAssets.value].content;
        parseInputs();
    });
    preAsset.addEventListener('change', () => {
        preInput.value = formAssetList[preAsset.value].content;
        parseInputs();
    });
    postAsset.addEventListener('change', () => {
        postInput.value = formAssetList[postAsset.value].content;
        parseInputs();
    });

    codeInput.addEventListener('input', parseInputs);
    preInput.addEventListener('input', parseInputs);
    postInput.addEventListener('input', parseInputs);

    const getSolverResult = (solverName, program, precond, postcond) => {
        return fetch(`/api/solver/${solverName}/verify`, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify({ program, precond, postcond, })
        })
        .then(res => res.json())
        .catch(err => {
            console.error(err);
            return { answer: `Error: ${err.message}` };
        });
    };

    fetch('/api/solvers')
        .then(res => res.json())
        .then(data => {
            data.solvers.forEach(solver => solversList.push(solver));
        })
        .catch(err => {
            console.error(err);
            alert(`Failed to fetch solvers list, this is a hard error: ${err.message}`);
        });

    fetch('/api/code/assets')
        .then(res => res.json())
        .then(data => {
            data.assets.forEach(asset => {
                const option = document.createElement('option');
                codeAssetList[asset.name] = asset;
                option.value = asset.name;
                option.textContent = asset.name;
                codeAssets.appendChild(option);
            });
            codeInput.value = codeAssetList[codeAssets.value].content;
            parseInputs();
        })
        .catch(err => {
            console.error(err);
        });

    fetch('/api/formulas/assets')
        .then(res => res.json())
        .then(data => {
            data.assets.forEach(asset => {
                const option = document.createElement('option');
                formAssetList[asset.name] = asset;
                option.value = asset.name;
                option.textContent = asset.name;
                preAsset.appendChild(option);
                postAsset.appendChild(option.cloneNode(true));
            });
            preInput.value = formAssetList[preAsset.value].content;
            postInput.value = formAssetList[postAsset.value].content;
            parseInputs();
        })
        .catch(err => {
            console.error(err);
        });


};
