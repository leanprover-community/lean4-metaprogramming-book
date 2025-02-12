/** Modifies the "Suggest an edit" button of mdbook,

* changing it to a link to the Lean4 web editor.
* Note that the modification is done on the HTML side to prevent the original icon from appearing for a moment.
*/
function filePlay() {
  const playButtonIcon = document.querySelector("#lean-play-button");

  const playButtonLink = playButtonIcon.parentElement;

  playButtonLink.href = playButtonLink.href.replace(/\.md$/, ".lean");

  playButtonLink.href = playButtonLink.href.replace(
    "/md/",
    "/lean/",
  );

  fetch(playButtonLink.href)
    .then((response) => response.text())
    .then((body) => {
      const escaped_code = encodeURIComponent(body);
      const url = `https://live.lean-lang.org/#code=${escaped_code}`;
      playButtonLink.href = url;
    });
}

filePlay();