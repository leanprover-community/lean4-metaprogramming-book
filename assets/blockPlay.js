/**
 * Add a button to jump to the Lean 4 web playground within the Lean 4 code block
 */
function blockPlay() {
  const array = Array.from(document.querySelectorAll(".language-lean"));
  for (const code_block of array) {
    const pre_block = code_block.parentElement;

    const escaped_code = encodeURIComponent(code_block.textContent);
    const url = `https://live.lean-lang.org/#code=${escaped_code}`;

    const buttons = pre_block.querySelector(".buttons");
    const leanWebButton = document.createElement("button");
    leanWebButton.className = "fa fa-external-link lean-web-button";
    leanWebButton.hidden = true;
    leanWebButton.title = "Run on lean4 playground";
    leanWebButton.setAttribute("aria-label", leanWebButton.title);

    buttons.insertBefore(leanWebButton, buttons.firstChild);

    leanWebButton.addEventListener("click", (e) => {
      open(url);
    });
  }
}

blockPlay();