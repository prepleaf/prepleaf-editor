import Draft from 'draft-js';

const { Modifier, EditorState } = Draft;

let count = 0;
export const INLINE_EQUATION = 'ie';

export function insertText(editorState, content) {
	const selectionState = editorState.getSelection();
	const contentState = editorState.getCurrentContent();
	const contentStateWithLink = Modifier.replaceText(
		contentState,
		selectionState,
		content
	);

	const newEditorState = EditorState.push(
		editorState,
		contentStateWithLink,
		'insert-characters'
	);
	return newEditorState;
}
