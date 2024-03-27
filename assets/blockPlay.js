Array.from(document.querySelectorAll(".language-lean")).forEach(function (code_block) {
  let pre_block = code_block.parentElement;

  // create a link to lean4 web editor
  let escaped_code = encodeURIComponent(code_block.textContent);
  let url = `https://live.lean-lang.org/#code=${escaped_code}`;

  // create a button
  let buttons = pre_block.querySelector(".buttons");
  let leanWebButton = document.createElement('button');
  leanWebButton.className = 'fa fa-external-link lean-web-button';
  leanWebButton.hidden = true;
  leanWebButton.title = 'Run on lean4 playground';
  leanWebButton.setAttribute('aria-label', leanWebButton.title);

  // insert the button
  buttons.insertBefore(leanWebButton, buttons.firstChild);

  // open the link when the button is clicked
  leanWebButton.addEventListener('click', function (e) {
    open(url);
  });
});