import { Map } from 'immutable';
import React from 'react';
import PropTypes from 'prop-types';
import {
	Editor,
	EditorState,
	convertFromRaw,
	convertToRaw,
	RichUtils,
	getDefaultKeyBinding,
	KeyBindingUtil,
	SelectionState,
	Modifier,
} from 'draft-js';
import 'draft-js/dist/Draft.css';

import TeXBlock from './TeXBlock';
import ImageBlock from './ImageBlock';
import { insertTeXBlock } from './modifiers/insertTeXBlock';
import { removeTeXBlock } from './modifiers/removeTeXBlock';
import { insertText } from './modifiers/insertText';
import {
	insertInlineEquation,
	INLINE_EQUATION,
} from './modifiers/insertInlineEquation';
import { insertImageBlock } from './modifiers/insertImageBlock';
import decorators from './decorators';
import InlineEquation from './components/InlineEquation';
import Button from './Button';
import { PrpeleafEditorGlobalContext } from './contexts';
import { EditEquation } from './decorators/inline-equation';
import './main.css';

const customStyleMap = {
	super: { verticalAlign: 'super', fontSize: '.8rem' },
	sub: { verticalAlign: 'sub', fontSize: '0.8rem' },
	equation: { marginLeft: '1px', marginRight: '1px', fontStyle: 'italic' },
};

const { hasCommandModifier } = KeyBindingUtil;

const katexCssCdn = (
	<link
		rel="stylesheet"
		href="https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.11.1/katex.min.css"
		integrity="sha256-V8SV2MO1FUb63Bwht5Wx9x6PVHNa02gv8BgH/uH3ung="
		crossOrigin="anonymous"
	/>
);

const keyBindingFn = (e) => {
	if (e.keyCode === 120) {
		return 'insert_image';
	}
	if (hasCommandModifier(e)) {
		if (e.keyCode === 188) {
			e.preventDefault();
			return 'sub';
		}
		if (e.keyCode === 190) {
			e.preventDefault();
			return 'super';
		}
		if (e.keyCode === 69) {
			e.preventDefault();
			return 'equation';
		}
	}
	return getDefaultKeyBinding(e);
};

export class TeXEditor extends React.Component {
	constructor(props, context) {
		super(props, context);

		const { rawContent } = props;
		let contentEditorState;
		if (typeof rawContent === 'undefined') {
			contentEditorState = EditorState.createEmpty(decorators);
		} else {
			let modifiedRawContent;
			if (typeof rawContent === 'object') {
				modifiedRawContent = {
					entityMap: {},
					blocks: [],
					...rawContent,
				};
			} else {
				modifiedRawContent = {
					entityMap: {},
					blocks: [],
					...JSON.parse(rawContent),
				};
			}
			contentEditorState = EditorState.createWithContent(
				convertFromRaw(modifiedRawContent),
				decorators
			);
		}

		this.state = {
			editorState: contentEditorState,
			liveTeXEdits: Map(),
			imageEdits: Map(),
			pasteEquationInline: false,
		};

		this._focus = () => this.editorRef.focus();
		this._onChange = (editorState) => this.setState({ editorState });

		this._toggleName = (editorState, name) => {
			this._onChange(RichUtils.toggleInlineStyle(editorState, name));
		};

		this._handleKeyCommand = (command, editorState) => {
			if (['super', 'sub'].indexOf(command) > -1) {
				this._toggleName(editorState, command);
				return true;
			}
			if ('equation' === command) {
				this.markAsInlineEquation();
			}

			if ('insert_image' === command) {
				this._insertImage();
			}

			var newState = RichUtils.handleKeyCommand(editorState, command);
			if (newState) {
				this._onChange(newState);
				return true;
			}
			return false;
		};

		this._removeTeX = (blockKey) => {
			var { editorState, liveTeXEdits, imageEdits } = this.state;
			this.setState({
				liveTeXEdits: liveTeXEdits.remove(blockKey),
				imageEdits: imageEdits.remove(blockKey),
				editorState: removeTeXBlock(editorState, blockKey),
			});
		};

		this._insertTeX = () => {
			this.setState({
				liveTeXEdits: Map(),
				editorState: insertTeXBlock(this.state.editorState),
			});
		};
	}
	markAsInlineEquation = () => {
		this.setState({
			editorState: insertInlineEquation(this.state.editorState),
		});
	};
	toggleSuper = (e) => {
		e.preventDefault();
		e.stopPropagation();
		const { editorState } = this.state;
		this._toggleName(editorState, 'super');
	};
	toggleSub = () => {
		const { editorState } = this.state;
		this._toggleName(editorState, 'sub');
	};
	toggleEquation = () => {
		const { editorState } = this.state;
		this._toggleName(editorState, 'equation');
	};

	_insertImage = () => {
		this.setState({
			imageEdits: Map(),
			editorState: insertImageBlock(this.state.editorState),
		});
	};
	get value() {
		const { editorState } = this.state;
		return {
			rawContent: convertToRaw(editorState.getCurrentContent()),
		};
	}

	_blockRenderer = (block) => {
		const { getImagePolicy, readOnly } = this.props;
		if (block.getType() === 'atomic') {
			const contentState = this.state.editorState.getCurrentContent();
			const type = contentState.getEntity(block.getEntityAt(0)).getType();
			if (type === 'TOKEN') {
				return {
					component: TeXBlock,
					editable: false,
					props: {
						onStartEdit: (blockKey) => {
							var { liveTeXEdits } = this.state;
							this.setState({
								liveTeXEdits: liveTeXEdits.set(blockKey, true),
							});
						},
						onFinishEdit: (blockKey, newContentState) => {
							var { liveTeXEdits } = this.state;
							this.setState({
								liveTeXEdits: liveTeXEdits.remove(blockKey),
								editorState: EditorState.createWithContent(newContentState, decorators),
							});
						},
						onRemove: (blockKey) => this._removeTeX(blockKey),
						readOnly,
					},
				};
			}

			if (type === 'IMAGE') {
				return {
					component: ImageBlock,
					editable: false,
					props: {
						onStartEdit: (blockKey) => {
							var { imageEdits } = this.state;
							this.setState({
								imageEdits: imageEdits.set(blockKey, true),
							});
						},
						onFinishEdit: (blockKey, newContentState) => {
							var { imageEdits } = this.state;
							this.setState({
								imageEdits: imageEdits.remove(blockKey),
								editorState: EditorState.createWithContent(newContentState, decorators),
							});
						},
						onRemove: (blockKey) => this._removeTeX(blockKey),
						getImagePolicy,
						readOnly,
					},
				};
			}
			if (type === INLINE_EQUATION) {
				return {
					component: InlineEquation,
				};
			}
		} else if (block.getType() === 'unstyled') {
		}
		return null;
	};

	resetEditor() {
		let contentEditorState = EditorState.createEmpty(decorators);
		this.setState({
			editorState: contentEditorState,
			liveTeXEdits: Map(),
		});
	}

	componentDidMount() {
		const { customRef } = this.props;
		customRef && customRef(this);
		this.refreshPasteEquationFlag();
	}
	componentWillUnmount() {
		const { customRef } = this.props;
		customRef && customRef(null);
	}
	refreshPasteEquationFlag = () => {
		if (window.localStorage.getItem('pasteEquationFlag') === 'inline') {
			this.setState({ pasteEquationInline: true });
		} else {
			this.setState({ pasteEquationInline: false });
		}
	};
	handlePasteEquationFlagChange = (e) => {
		window.localStorage.setItem(
			'pasteEquationFlag',
			e.target.checked ? 'inline' : 'block'
		);
		this.refreshPasteEquationFlag();
	};
	get contextValue() {
		return {
			openInlineEquationEditor: (blockKey, start, end, text) => {
				this.setState({ editInlineEquation: { blockKey, start, end, text } });
			},
			changeText: this.changeText,
			readOnly: this.props.readOnly,
		};
	}
	changeText = (blockKey, start, end, text) => {
		const editorState = this.state.editorState;
		const emptySelection = SelectionState.createEmpty(blockKey);
		const selection = emptySelection.merge({
			anchorOffset: start,
			focusOffset: end,
		});
		const newContentState = Modifier.replaceText(
			editorState.getCurrentContent(),
			selection,
			text
		);
		const newEditorState = EditorState.createWithContent(
			newContentState,
			decorators
		);
		this.setState({
			editorState: newEditorState,
			editInlineEquation: undefined,
		});
	};
	/**
	 * While editing TeX, set the Draft editor to read-only. This allows us to
	 * have a textarea within the DOM.
	 */
	render() {
		const { readOnly } = this.props;
		const { pasteEquationInline } = this.state;
		if (readOnly) {
			return (
				<div>
					{katexCssCdn}
					<PrpeleafEditorGlobalContext.Provider value={this.contextValue}>
						<Editor
							customStyleMap={customStyleMap}
							blockRendererFn={this._blockRenderer}
							editorState={this.state.editorState}
							handleKeyCommand={this._handleKeyCommand}
							keyBindingFn={keyBindingFn}
							onChange={this._onChange}
							readOnly={
								readOnly ||
								this.state.liveTeXEdits.count() ||
								this.state.imageEdits.count()
							}
							ref={this.handleEditorRef}
							spellCheck={true}
						/>
					</PrpeleafEditorGlobalContext.Provider>
				</div>
			);
		}
		return (
			<div className="prepleaf-editor">
				{katexCssCdn}
				<div className="TeXEditor-toolbar">
					<div className="TeXEditor-toolbar-list">
						<Button
							onMouseDown={this.toggleEquation}
							className="TeXEditor-insert-button hidden"
						>
							inline equation
						</Button>
						<Button onMouseDown={this.toggleSub} className="TeXEditor-insert-button">
							X<sub>2</sub>
						</Button>
						<Button
							onMouseDown={this.toggleSuper}
							className="TeXEditor-insert-button"
						>
							X<sup>2</sup>
						</Button>
						<Button onMouseDown={this._insertTeX} className="TeXEditor-insert-button">
							Equation
						</Button>
						<Button
							onMouseDown={this._insertImage}
							className="TeXEditor-insert-button"
						>
							Image
						</Button>
					</div>
					<div>
						{this.state.editInlineEquation ? (
							<EditEquation
								value={this.state.editInlineEquation.text}
								onCancel={() => this.setState({ editInlineEquation: undefined })}
								onChange={(text) => {
									this.changeText(
										this.state.editInlineEquation.blockKey,
										this.state.editInlineEquation.start,
										this.state.editInlineEquation.end,
										text
									);
								}}
							/>
						) : null}
						<div style={{}}>
							<label>
								<input
									checked={pasteEquationInline}
									onChange={this.handlePasteEquationFlagChange}
									type="checkbox"
								/>
								Paste Equation Inline
							</label>
						</div>
						<div style={{ display: 'none' }}>
							For inline eqn use $equatoin in here$: $\frac{'{2}{3}$'}
						</div>
					</div>
				</div>
				<div className="TeXEditor-root">
					<div
						className="TeXEditor-editor"
						style={{ border: 'solid 1px #777' }}
						onClick={this._focus}
					>
						<PrpeleafEditorGlobalContext.Provider value={this.contextValue}>
							<Editor
								handlePastedFiles={(files) => {
									const { editorState } = this.state;
									this.setState({
										editorState: insertImageBlock(editorState, files[0]),
									});
									return 'handled';
								}}
								handleDroppedFiles={(selection, files) => {
									const updatedSelectionEditorState = EditorState.acceptSelection(
										this.state.editorState,
										selection
									);
									this.setState({
										editorState: insertImageBlock(updatedSelectionEditorState, files[0]),
									});
									return 'handled';
								}}
								handlePastedText={(text, html, editorState) => {
									if (text.indexOf('$$') === 0 && text.substring(text.length - 2)) {
										if (pasteEquationInline) {
											const newEditorState = insertText(
												editorState,
												text.substring(1, text.length - 1) + ' '
											);
											this.setState({ editorState: newEditorState });
											return 'handled';
										}
										const content = text.substring(2, text.length - 2);
										this.setState({
											editorState: insertTeXBlock(editorState, content),
										});
										return 'handled';
									}
									return 'not-handled';
								}}
								customStyleMap={customStyleMap}
								blockRendererFn={this._blockRenderer}
								editorState={this.state.editorState}
								handleKeyCommand={this._handleKeyCommand}
								keyBindingFn={keyBindingFn}
								onChange={this._onChange}
								placeholder="Start a document..."
								readOnly={
									readOnly ||
									this.state.liveTeXEdits.count() ||
									this.state.imageEdits.count()
								}
								ref={this.handleEditorRef}
								spellCheck={true}
							/>
						</PrpeleafEditorGlobalContext.Provider>
					</div>
				</div>
			</div>
		);
	}

	handleEditorRef = (ref) => {
		this.editorRef = ref;
	};
}

TeXEditor.propTypes = {
	readOnly: PropTypes.bool.isRequired,
};

TeXEditor.defaultProps = {
	readOnly: false,
};

export default TeXEditor;
