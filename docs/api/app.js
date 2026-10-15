/* CountingLib selected API browser. No external runtime or HTML injection. */
'use strict';
(() => {
  const $ = (id) => document.getElementById(id);
  const controls = ['query', 'category', 'family', 'module', 'kind'];
  const pageSize = 20;
  let catalog;
  let families;
  let matches = [];
  let visible = pageSize;
  let timer;
  let target = '';

  function element(tag, text, className) {
    const result = document.createElement(tag);
    if (text !== undefined) result.textContent = text;
    if (className) result.className = className;
    return result;
  }

  function link(label, href, className) {
    const result = element('a', label, className);
    result.href = href;
    return result;
  }

  function button(label, action) {
    const result = element('button', label, 'text-button');
    result.type = 'button';
    result.addEventListener('click', action);
    return result;
  }

  function filterState() {
    return Object.fromEntries(controls.map((id) => [id, $(id).value]));
  }

  function fragment(declaration) {
    const params = new URLSearchParams();
    for (const [key, value] of Object.entries(filterState())) {
      if (value) params.set(key === 'query' ? 'q' : key, value);
    }
    if (declaration) params.set('decl', declaration);
    const result = params.toString();
    return result ? '#' + result : location.pathname + location.search;
  }

  function updateLocation() {
    history.replaceState(null, '', fragment(target));
  }

  function selectOptions(id, values) {
    for (const [value, label] of values) {
      const option = element('option', label);
      option.value = value;
      $(id).append(option);
    }
  }

  function contractDetails(family, heading = 'Promises and cost contract') {
    const detail = element('details', undefined, 'api-detail');
    detail.append(element('summary', heading));
    detail.addEventListener('toggle', () => {
      if (!detail.open || detail.dataset.loaded) return;
      detail.dataset.loaded = 'true';
      const list = element('dl', undefined, 'contract-list');
      for (const field of family.fields) {
        list.append(element('dt', field.label), element('dd', field.text));
      }
      detail.append(list);
      if (family.paper_note) detail.append(element('p', family.paper_note, 'paper-note'));
    });
    return detail;
  }

  function typeDetails(row, key, label) {
    const detail = element('details', undefined, 'api-detail');
    detail.append(element('summary', label));
    detail.addEventListener('toggle', () => {
      if (!detail.open || detail.dataset.loaded) return;
      detail.dataset.loaded = 'true';
      const value = key === 'specification' ? row[key] : row.name + ' :\n' + row[key];
      detail.append(element('p', key === 'type'
        ? 'Complete elaborated type (Lean pp.all). Explicit arguments and universes are retained.'
        : key === 'readable_type' ? 'Lean pretty-printed type; implicit arguments or proof terms may be elided. Open Full Lean type for explicit detail.'
          : 'Complete exported specification body (Lean pp.all).', 'detail-note'));
      const pre = element('pre', undefined, 'full-type');
      pre.tabIndex = 0;
      pre.setAttribute('aria-label', label + ' for ' + row.display_name);
      pre.append(element('code', value));
      const actions = element('div', undefined, 'type-controls');
      const expand = button('Expand height', () => {
        const expanded = pre.classList.toggle('expanded');
        expand.textContent = expanded ? 'Limit height' : 'Expand height';
        expand.setAttribute('aria-expanded', String(expanded));
      });
      expand.setAttribute('aria-expanded', 'false');
      const copy = button('Copy', async () => {
        try {
          await navigator.clipboard.writeText(value);
          copy.textContent = 'Copied';
          setTimeout(() => { copy.textContent = 'Copy'; }, 1800);
        } catch (_) {
          copy.textContent = 'Select the type to copy';
          pre.focus();
        }
      });
      actions.append(expand, copy);
      detail.append(actions, pre);
    });
    return detail;
  }

  function card(row) {
    const family = families.get(row.family);
    const isTarget = row.name === target || row.display_name === target;
    const article = element('article', undefined, 'api-card' + (isTarget ? ' is-target' : ''));
    article.id = 'declaration-' + row.name;
    const tags = element('div', undefined, 'card-tags');
    tags.append(element('span', ({flagships: 'FLAGSHIP', tools: 'TOOL', core: 'CORE / ALGORITHM'})[row.category] || row.category.toUpperCase(), 'tag'));
    tags.append(element('span', row.kind.replaceAll('-', ' '), 'tag kind'));
    if (row.role === 'client') tags.append(element('span', 'client', 'tag client'));
    const title = element('h3', undefined, 'declaration-name');
    title.append(link(row.display_name, fragment(row.name)));
    article.append(tags, element('p', family.title, 'family-label'), title);
    if (row.summary) article.append(element('p', row.summary, 'record-summary'));
    const importLine = element('p', undefined, 'module-line');
    importLine.append(document.createTextNode('Import '), element('code', row.import));
    const moduleLine = element('p', undefined, 'module-line');
    moduleLine.append(document.createTextNode('Provider '), element('code', row.module));
    article.append(importLine, moduleLine);
    if (row.display_name !== row.name) {
      const canonical = element('p', undefined, 'canonical-name');
      canonical.append(document.createTextNode('Export alias of '), element('code', row.name),
        document.createTextNode('. One kernel declaration.'));
      article.append(canonical);
    }
    const preview = (row.readable_type || row.type).replace(/\s+/g, ' ');
    article.append(element('pre', preview.length > 230 ? preview.slice(0, 230) + ' …' : preview, 'type-preview'));
    const actions = element('div', undefined, 'card-actions');
    actions.append(link('Source ↗', row.source_url), link('Permalink', fragment(row.name)));
    if (family.paper_url) actions.append(link('Paper ↗', family.paper_url));
    else if (family.reference_url) actions.append(link('Paper references ↗', family.reference_url));
    if (family.original_source_url) actions.append(link('Original Lean ↗', family.original_source_url));
    article.append(actions);
    const readableType = row.readable_type ? typeDetails(row, 'readable_type', 'Readable Lean type') : null;
    if (readableType) article.append(readableType);
    const fullType = typeDetails(row, 'type', 'Full Lean type');
    article.append(fullType);
    if (row.specification) article.append(typeDetails(row, 'specification', 'Specification body'));
    article.append(contractDetails(family));
    if (row.original_declaration) {
      article.append(element('p', 'Original declaration: ' + row.original_declaration +
        (row.paper_item ? ' · Paper item ' + row.paper_item : ''), 'paper-note'));
    }
    if (isTarget) (readableType || fullType).open = true;
    return article;
  }

  function renderContext() {
    const box = $('family-context');
    box.replaceChildren();
    const family = families.get($('family').value);
    const unknownTarget = target && !catalog.declarations.some((row) => row.name === target || row.display_name === target);
    box.hidden = !family && !unknownTarget;
    if (unknownTarget) box.append(element('p', 'The requested declaration is not in this selected catalog. Search the available interfaces below or follow the source reference.', 'notice'));
    if (!family) return;
    const inner = element('section', undefined, 'family-context');
    inner.append(element('h3', family.title));
    if (family.public_import) inner.append(element('p', 'Public import: ' + family.public_import));
    inner.append(contractDetails(family, 'Read the family contract'));
    const actions = element('div', undefined, 'card-actions');
    if (family.paper_url) actions.append(link('Paper ↗', family.paper_url));
    else if (family.reference_url) actions.append(link('Paper references ↗', family.reference_url));
    if (family.original_source_url) actions.append(link('Original Lean release ↗', family.original_source_url));
    inner.append(actions);
    box.append(inner);
  }

  function renderResults(start = 0) {
    const panel = $('results');
    if (start === 0) panel.replaceChildren();
    if (matches.length === 0) {
      const empty = element('div', undefined, 'empty-state');
      empty.append(element('h3', 'No declarations match.'),
        element('p', 'Try fewer words, a shorter name, or reset the filters.'));
      panel.append(empty);
    } else {
      const fragment = document.createDocumentFragment();
      for (const row of matches.slice(start, visible)) fragment.append(card(row));
      panel.append(fragment);
    }
    $('result-count').textContent = matches.length + ' result' + (matches.length === 1 ? '' : 's') +
      (matches.length > visible ? ' · showing ' + visible : '');
    $('load-more').hidden = matches.length <= visible;
    panel.setAttribute('aria-busy', 'false');
  }

  function search(options = {}) {
    const state = filterState();
    const query = state.query.trim().toLocaleLowerCase();
    const tokens = query.split(/\s+/).filter(Boolean);
    matches = catalog.declarations.filter((row) =>
      (!state.category || row.category === state.category) &&
      (!state.family || row.family === state.family) &&
      (!state.module || row.module === state.module) &&
      (!state.kind || row.kind === state.kind) &&
      tokens.every((token) => row.search_text.includes(token)));
    if (query) {
      const score = (row) => row.display_name.toLocaleLowerCase() === query ? 0
        : row.display_name.toLocaleLowerCase().endsWith('.' + query) ? 1
        : row.display_name.toLocaleLowerCase().includes(query) ? 2 : 3;
      matches.sort((a, b) => score(a) - score(b) || a.display_name.localeCompare(b.display_name));
    }
    visible = pageSize;
    const index = target ? matches.findIndex((row) => row.name === target || row.display_name === target) : -1;
    if (index >= 0) visible = Math.max(pageSize, Math.ceil((index + 1) / pageSize) * pageSize);
    renderContext();
    renderResults();
    if (!options.fromLocation) updateLocation();
    if (options.scrollTarget && index >= 0) {
      requestAnimationFrame(() => document.getElementById('declaration-' + matches[index].name)
        ?.scrollIntoView({block: 'start'}));
    }
  }

  function readLocation(scrollTarget = false) {
    clearTimeout(timer);
    const params = new URLSearchParams(location.hash.slice(1));
    for (const id of controls) $(id).value = params.get(id === 'query' ? 'q' : id) || '';
    target = params.get('decl') || '';
    const row = target && catalog.declarations.find((item) => item.name === target || item.display_name === target);
    if (row) {
      // A declaration permalink remains usable even if its old filter context changed.
      const state = filterState();
      const excludes = (state.category && row.category !== state.category) ||
        (state.family && row.family !== state.family) ||
        (state.module && row.module !== state.module) || (state.kind && row.kind !== state.kind) ||
        state.query.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean)
          .some((token) => !row.search_text.includes(token));
      if (excludes) for (const id of controls) $(id).value = '';
    }
    search({fromLocation: true, scrollTarget});
  }

  function filterChanged() {
    clearTimeout(timer);
    target = '';
    search();
  }

  async function initialize() {
    try {
      const response = await fetch('api-data.json');
      if (!response.ok) throw new Error('Catalog HTTP ' + response.status);
      catalog = await response.json();
      families = new Map(catalog.families.map((family) => [family.id, family]));
      for (const row of catalog.declarations) {
        row.search_text = [row.name, row.display_name, row.module, row.import, row.type,
          families.get(row.family).title].join('\n').toLocaleLowerCase();
      }
      selectOptions('family', catalog.families.map((family) => [family.id, family.title]));
      selectOptions('module', [...new Set(catalog.declarations.map((row) => row.module))].sort().map((value) => [value, value]));
      selectOptions('kind', [...new Set(catalog.declarations.map((row) => row.kind))].sort().map((value) => [value, value.replaceAll('-', ' ')]));
      $('search-form').addEventListener('submit', (event) => {
        event.preventDefault(); clearTimeout(timer); filterChanged();
      });
      $('query').addEventListener('input', () => {
        clearTimeout(timer); timer = setTimeout(filterChanged, 140);
      });
      for (const id of controls.slice(1)) $(id).addEventListener('change', filterChanged);
      $('reset').addEventListener('click', () => {
        clearTimeout(timer);
        for (const id of controls) $(id).value = '';
        filterChanged(); $('query').focus();
      });
      for (const action of document.querySelectorAll('[data-query]')) {
        action.addEventListener('click', () => {
          for (const id of controls) $(id).value = '';
          $('query').value = action.dataset.query;
          filterChanged(); $('query').focus();
        });
      }
      for (const action of document.querySelectorAll('[data-family]')) {
        action.addEventListener('click', () => {
          for (const id of controls) $(id).value = '';
          $('family').value = action.dataset.family;
          filterChanged(); $('results-title').scrollIntoView({block: 'start'});
        });
      }
      $('load-more').addEventListener('click', () => {
        const previous = Math.min(visible, matches.length);
        visible += pageSize; renderResults(previous);
        const firstNewLink = $('results').children[previous]?.querySelector('h3 a');
        if (firstNewLink) firstNewLink.focus({preventScroll: true});
      });
      window.addEventListener('hashchange', () => readLocation(true));
      document.addEventListener('keydown', (event) => {
        if (event.key === '/' && !event.ctrlKey && !event.metaKey && !event.altKey &&
          !['INPUT', 'TEXTAREA', 'SELECT'].includes(document.activeElement.tagName) &&
          !document.activeElement.isContentEditable) {
          event.preventDefault(); $('query').focus();
        }
      });
      readLocation(true);
    } catch (error) {
      $('load-error').hidden = false;
      $('results').setAttribute('aria-busy', 'false');
      $('result-count').textContent = 'Catalog unavailable';
      for (const id of controls) $(id).disabled = true;
      document.querySelector('.search-submit').disabled = true;
      // Keep the failure visible without logging signatures or private environment data.
      console.error('CountingLib API catalog could not be loaded.');
    }
  }
  initialize();
})();
