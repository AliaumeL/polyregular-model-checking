

window.onload = () => {

    const inputForm     = document.getElementById('user-input');
    const codeAssets    = document.getElementById('code-assets');
    const codeInput     = document.getElementById('code');
    const preAsset      = document.getElementById('pre-assets');
    const preInput      = document.getElementById('pre');
    const postAsset     = document.getElementById('post-assets');
    const postInput     = document.getElementById('post');
    const output        = document.getElementById('output-view');


    const codeAssetList = {};
    const formAssetList = {};

    /* prevent submission from inputForm, and register our own handler */
    inputForm.addEventListener('submit', (e) => {
        e.preventDefault();
        const program  = codeInput.value;
        const precond  = preInput.value;
        const postcond = postInput.value;

        output.textContent = 'Verifying...';

        fetch('/api/verify/', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify({ program, precond, postcond })
            })
            .then(res => res.json())
            .then(data => {
                output.innerHTML = '';
                const banner = document.createElement('p');
                if (data.error) {
                    banner.textContent = data.error;
                    banner.classList.add('error');
                } else {
                    banner.textContent = 'Verification completed';
                    banner.classList.add('success');
                }
                output.appendChild(banner);
                /* add hrule */
                output.appendChild(document.createElement('hr'));

                const ul = document.createElement('ul');
                data.responses.forEach(response => {
                    const li = document.createElement('li');
                    const solverUsed = response.solverUsed;
                    const answer     = response.answer;

                    if (answer === 'Unsat') {
                        li.textContent = `${solverUsed}: OK!`;
                        li.classList.add('success');
                    } else if (answer === 'Sat') {
                        li.textContent = `${solverUsed}: NO!`;
                        li.classList.add('error');
                    } else if (answer === 'Unknown') {
                        li.textContent = `${solverUsed}: ???`;
                        li.classList.add('neutral');
                    } else {
                        li.textContent = `${solverUsed}: ${answer}`;
                        li.classList.add('error');
                    }
                    ul.appendChild(li);
                });
                output.appendChild(ul);
                output.appendChild(document.createElement('hr'));
                const simpleCode = document.createElement('pre');
                simpleCode.textContent = data.simplified;
                output.appendChild(simpleCode);
            })
            .catch(err => {
                console.error(err);
            });
    });

    codeAssets.addEventListener('change', () => {
        codeInput.value = codeAssetList[codeAssets.value].content;
    });
    preAsset.addEventListener('change', () => {
        preInput.value = formAssetList[preAsset.value].content;
    });
    postAsset.addEventListener('change', () => {
        postInput.value = formAssetList[postAsset.value].content;
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
        });


};
