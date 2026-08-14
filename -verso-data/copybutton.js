
function addToggleButtonToElement(elementId, className = 'tpil-hide-prefix') {
    const element = document.getElementById(elementId);
    if (!element) {
        console.error(`Element with ID '${elementId}' not found`);
        return false;
    }

    // Create container wrapper if it doesn't exist
    let container = element.parentElement;
    if (!container.classList.contains('code-container')) {
        container = document.createElement('div');
        container.className = 'code-container';
        container.classList.toggle(className);

        // Insert container before element
        element.parentNode.insertBefore(container, element);

        // Move element into container
        container.appendChild(element);
    }

    // Remove existing toggle button if present
    const existingBtn = container.querySelector('.toggle-btn');
    if (existingBtn) {
        existingBtn.remove();
    }

    // Create toggle button
    const toggleBtn = document.createElement('button');
    toggleBtn.className = 'toggle-btn';
    toggleBtn.title = 'Show hidden lines';
    toggleBtn.innerHTML = `
        <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
            <path d="M12 4.5C7 4.5 2.73 7.61 1 12c1.73 4.39 6 7.5 11 7.5s9.27-3.11 11-7.5c-1.73-4.39-6-7.5-11-7.5zM12 17c-2.76 0-5-2.24-5-5s2.24-5 5-5 5 2.24 5 5-2.24 5-5 5zm0-8c-1.66 0-3 1.34-3 3s1.34 3 3 3 3-1.34 3-3-1.34-3-3-3z"/>
        </svg>
    `;

    // Add click event listener
    toggleBtn.addEventListener('click', () => {
        container.classList.toggle(className);

        // Update icon based on state
        const isHidden = container.classList.contains(className);
        toggleBtn.innerHTML = !isHidden ? `
            <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
                <path d="M12 7c2.76 0 5 2.24 5 5 0 .65-.13 1.26-.36 1.83l2.92 2.92c1.51-1.26 2.7-2.89 3.43-4.75-1.73-4.39-6-7.5-11-7.5-1.4 0-2.74.25-3.98.7l2.16 2.16C10.74 7.13 11.35 7 12 7zM2 4.27l2.28 2.28.46.46C3.08 8.3 1.78 10.02 1 12c1.73 4.39 6 7.5 11 7.5 1.55 0 3.03-.3 4.38-.84l.42.42L19.73 22 21 20.73 3.27 3 2 4.27zM7.53 9.8l1.55 1.55c-.05.21-.08.43-.08.65 0 1.66 1.34 3 3 3 .22 0 .44-.03.65-.08l1.55 1.55c-.67.33-1.41.53-2.2.53-2.76 0-5-2.24-5-5 0-.79.2-1.53.53-2.2zm4.31-.78l3.15 3.15.02-.16c0-1.66-1.34-3-3-3l-.17.01z"/>
            </svg>
        ` : `
            <svg class="toggle-icon" viewBox="0 0 24 24" fill="currentColor">
                <path d="M12 4.5C7 4.5 2.73 7.61 1 12c1.73 4.39 6 7.5 11 7.5s9.27-3.11 11-7.5c-1.73-4.39-6-7.5-11-7.5zM12 17c-2.76 0-5-2.24-5-5s2.24-5 5-5 5 2.24 5 5-2.24 5-5 5zm0-8c-1.66 0-3 1.34-3 3s1.34 3 3 3 3-1.34 3-3-1.34-3-3-3z"/>
            </svg>
        `;
        toggleBtn.title = isHidden ? 'Show hidden lines' : 'Hide lines';
    });

    // Position toggle button to the left of copy button if it exists
    const copyBtn = container.querySelector('.copy-btn');
    if (copyBtn) {
        container.insertBefore(toggleBtn, copyBtn);
    } else {
        container.appendChild(toggleBtn);
    }

    return true;
}

function addCopyButtonToElement(elementId, codeText) {
    const element = document.getElementById(elementId);
    if (!element) {
        console.error(`Element with ID '${elementId}' not found`);
        return false;
    }

    // Create container wrapper if it doesn't exist
    let container = element.parentElement;
    if (!container.classList.contains('code-container')) {
        container = document.createElement('div');
        container.className = 'tpil-code-container';

        // Insert container before element
        element.parentNode.insertBefore(container, element);

        // Move element into container
        container.appendChild(element);
    }

    // Remove existing copy button if present
    const existingBtn = container.querySelector('.copy-btn');
    if (existingBtn) {
        existingBtn.remove();
    }

    // Create copy button
    const copyBtn = document.createElement('button');
    copyBtn.className = 'copy-btn';
    copyBtn.title = 'Copy to clipboard';
    copyBtn.innerHTML = `
        <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
            <path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/>
        </svg>
    `;

    // Add click event listener
    copyBtn.addEventListener('click', async () => {
        try {
            // Copy the provided code text to clipboard
            await navigator.clipboard.writeText(codeText);

            // Show success feedback
            const originalText = copyBtn.innerHTML;
            copyBtn.innerHTML = `
                <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"/>
                </svg>
                Copied!
            `;
            copyBtn.classList.add('copied');

            // Reset after 2 seconds
            setTimeout(() => {
                copyBtn.innerHTML = originalText;
                copyBtn.classList.remove('copied');
            }, 2000);

        } catch (err) {
            // Fallback for older browsers
            fallbackCopyTextToClipboard(codeText);

            // Show feedback
            copyBtn.textContent = 'Copied!';
            setTimeout(() => {
                copyBtn.innerHTML = `
                    <svg class="copy-icon" viewBox="0 0 24 24" fill="currentColor">
                        <path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/>
                    </svg>
                `;
            }, 2000);
        }
    });

    // Add button to container
    container.appendChild(copyBtn);
    return true;
}

// Fallback function for older browsers
function fallbackCopyTextToClipboard(text) {
    const textArea = document.createElement('textarea');
    textArea.value = text;
    textArea.style.position = 'fixed';
    textArea.style.left = '-999999px';
    textArea.style.top = '-999999px';
    document.body.appendChild(textArea);
    textArea.focus();
    textArea.select();

    try {
        document.execCommand('copy');
    } catch (err) {
        console.error('Fallback: Oops, unable to copy', err);
    }

    document.body.removeChild(textArea);
}

// Expose API function globally
window.addCopyButtonToElement = addCopyButtonToElement;
window.addToggleButtonToElement = addToggleButtonToElement;
