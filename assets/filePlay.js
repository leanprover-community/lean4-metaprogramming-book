/**
 * Modifying the "Suggest an edit" button in mdbook
 * to link to the lean4 web editor
 */

// The `i` element in the icon part of the edit button.
const editButtonIcon = document.querySelector('#git-edit-button');
editButtonIcon.className = 'fa fa-play';

// The `a` element representing the edit button.
const editButtonLink = editButtonIcon.parentElement;
editButtonLink.title = 'Run on Lean 4 playground';
editButtonLink.ariaLabel = editButtonLink.title;

// Correct the `.md` extension to `.lean`.
editButtonLink.href = editButtonLink.href.replace(/\.md$/, '.lean');

// Correct the location of the directory where the Lean files are located.
editButtonLink.href = editButtonLink.href.replace('/md/', '/lean/');

editButtonLink.addEventListener('click', async function (e) {
  e.preventDefault();

  fetch(editButtonLink.href)
    .then(response => response.text())
    .then(body => {
      const escaped_code = encodeURIComponent(body);
      const url = `https://live.lean-lang.org/#code=${escaped_code}`;
      open(url);
    });
});