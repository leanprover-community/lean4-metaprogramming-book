/** クライアントの環境がPCかどうか判定する */
function isDesktop() {
  const userAgent = navigator.userAgent;
  const mobileRegex =
    /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i;
  return !mobileRegex.test(userAgent);
}

/** 本体の処理 */
function pageToc() {
  function forEach(elems, fun) {
    Array.prototype.forEach.call(elems, fun);
  }

  function getPagetoc() {
    return document.getElementsByClassName("pagetoc")[0];
  }

  function getPagetocElems() {
    return getPagetoc().children;
  }

  function getHeaders() {
    return document.getElementsByClassName("header");
  }

  // Un-active everything when you click it
  function forPagetocElem(fun) {
    forEach(getPagetocElems(), fun);
  }

  function getRect(element) {
    return element.getBoundingClientRect();
  }

  function overflowTop(container, element) {
    return getRect(container).top - getRect(element).top;
  }

  function overflowBottom(container, element) {
    return getRect(container).bottom - getRect(element).bottom;
  }

  let activeHref = location.href;

  const updateFunction = (elem = undefined) => {
    let id = elem;

    if (!id && location.href !== activeHref) {
      activeHref = location.href;
      forPagetocElem((el) => {
        if (el.href === activeHref) {
          id = el;
        }
      });
    }

    if (!id) {
      const elements = getHeaders();
      const margin = window.innerHeight / 3;

      forEach(elements, (el, i, arr) => {
        if (!id && getRect(el).top >= 0) {
          if (getRect(el).top < margin) {
            id = el;
          } else {
            id = arr[Math.max(0, i - 1)];
          }
        }
        // a very long last section
        // its heading is over the screen
        if (!id && i === arr.length - 1) {
          id = el;
        }
      });
    }

    forPagetocElem((el) => {
      el.classList.remove("active");
    });

    if (!id) return;

    forPagetocElem((el) => {
      if (id.href.localeCompare(el.href) === 0) {
        el.classList.add("active");
        const pagetoc = getPagetoc();
        if (overflowTop(pagetoc, el) > 0) {
          pagetoc.scrollTop = el.offsetTop;
        }
        if (overflowBottom(pagetoc, el) < 0) {
          pagetoc.scrollTop -= overflowBottom(pagetoc, el);
        }
      }
    });
  };

  const elements = getHeaders();

  if (elements.length > 2) {
    // Populate sidebar on load
    window.addEventListener("load", () => {
      const pagetoc = getPagetoc();
      const elements = getHeaders();
      forEach(elements, (el) => {
        const link = document.createElement("a");
        link.appendChild(document.createTextNode(el.text));
        link.href = el.hash;
        link.classList.add(`pagetoc-${el.parentElement.tagName}`);
        pagetoc.appendChild(link);
        link.onclick = () => {
          updateFunction(link);
        };
      });
      updateFunction();
    });

    // Handle active elements on scroll
    window.addEventListener("scroll", () => {
      updateFunction();
    });
  } else {
    document.getElementsByClassName("sidetoc")[0].remove();
  }
}

pageToc();